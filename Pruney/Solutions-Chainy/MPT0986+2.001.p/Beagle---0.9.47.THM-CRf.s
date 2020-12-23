%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:52 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 548 expanded)
%              Number of leaves         :   42 ( 205 expanded)
%              Depth                    :   17
%              Number of atoms          :  218 (1545 expanded)
%              Number of equality atoms :   56 ( 367 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(c_60,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_73,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_73])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_16,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_188,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_192,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_188])).

tff(c_257,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_260,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_257])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_192,c_260])).

tff(c_264,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_263])).

tff(c_95,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_99,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_12])).

tff(c_105,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_102])).

tff(c_110,plain,(
    ! [B_43,A_44] :
      ( k2_relat_1(k7_relat_1(B_43,A_44)) = k9_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_110])).

tff(c_123,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_119])).

tff(c_200,plain,(
    ! [A_62,B_63] :
      ( k9_relat_1(k2_funct_1(A_62),k9_relat_1(A_62,B_63)) = B_63
      | ~ r1_tarski(B_63,k1_relat_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_218,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_200])).

tff(c_225,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_62,c_218])).

tff(c_228,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_265,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_228])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_265])).

tff(c_270,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_24,plain,(
    ! [A_10,B_12] :
      ( k9_relat_1(k2_funct_1(A_10),k9_relat_1(A_10,B_12)) = B_12
      | ~ r1_tarski(B_12,k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_278,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_1') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_24])).

tff(c_359,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_362,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_362])).

tff(c_368,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_367,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_1') = k2_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_498,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_501,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_498])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_62,c_6,c_501])).

tff(c_505,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_1') = k2_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_548,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_551,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_548])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_551])).

tff(c_557,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_18,plain,(
    ! [A_9] :
      ( v2_funct_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_556,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_1') = k2_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_558,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_561,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_558])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_62,c_561])).

tff(c_567,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_172,plain,(
    ! [A_51] :
      ( k1_relat_1(k2_funct_1(A_51)) = k2_relat_1(A_51)
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_436,plain,(
    ! [A_83] :
      ( k9_relat_1(k2_funct_1(A_83),k2_relat_1(A_83)) = k2_relat_1(k2_funct_1(A_83))
      | ~ v1_relat_1(k2_funct_1(A_83))
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_445,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_270])).

tff(c_469,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_62,c_368,c_445])).

tff(c_34,plain,(
    ! [A_16] :
      ( k2_funct_1(k2_funct_1(A_16)) = A_16
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_322,plain,(
    ! [B_72,A_73] :
      ( k1_funct_1(B_72,k1_funct_1(k2_funct_1(B_72),A_73)) = A_73
      | ~ r2_hidden(A_73,k2_relat_1(B_72))
      | ~ v2_funct_1(B_72)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_820,plain,(
    ! [A_89,A_90] :
      ( k1_funct_1(k2_funct_1(A_89),k1_funct_1(A_89,A_90)) = A_90
      | ~ r2_hidden(A_90,k2_relat_1(k2_funct_1(A_89)))
      | ~ v2_funct_1(k2_funct_1(A_89))
      | ~ v1_funct_1(k2_funct_1(A_89))
      | ~ v1_relat_1(k2_funct_1(A_89))
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_322])).

tff(c_824,plain,(
    ! [A_90] :
      ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4',A_90)) = A_90
      | ~ r2_hidden(A_90,'#skF_1')
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_820])).

tff(c_852,plain,(
    ! [A_91] :
      ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4',A_91)) = A_91
      | ~ r2_hidden(A_91,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68,c_62,c_368,c_557,c_567,c_824])).

tff(c_56,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_861,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_56])).

tff(c_876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  
% 3.24/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.24/1.47  
% 3.24/1.47  %Foreground sorts:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Background operators:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Foreground operators:
% 3.24/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.24/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.24/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.24/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.24/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.24/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.47  
% 3.24/1.49  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.24/1.49  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.49  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.24/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.49  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.49  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.24/1.49  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.49  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.24/1.49  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.24/1.49  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 3.24/1.49  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.24/1.49  tff(f_65, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.24/1.49  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.24/1.49  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.24/1.49  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 3.24/1.49  tff(c_60, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_73, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.24/1.49  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_73])).
% 3.24/1.49  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_62, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_16, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.49  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_188, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.24/1.49  tff(c_192, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_188])).
% 3.24/1.49  tff(c_257, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.24/1.49  tff(c_260, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_257])).
% 3.24/1.49  tff(c_263, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_192, c_260])).
% 3.24/1.49  tff(c_264, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_263])).
% 3.24/1.49  tff(c_95, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.24/1.49  tff(c_99, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_95])).
% 3.24/1.49  tff(c_12, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.49  tff(c_102, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_12])).
% 3.24/1.49  tff(c_105, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_102])).
% 3.24/1.49  tff(c_110, plain, (![B_43, A_44]: (k2_relat_1(k7_relat_1(B_43, A_44))=k9_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.49  tff(c_119, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_105, c_110])).
% 3.24/1.49  tff(c_123, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_119])).
% 3.24/1.49  tff(c_200, plain, (![A_62, B_63]: (k9_relat_1(k2_funct_1(A_62), k9_relat_1(A_62, B_63))=B_63 | ~r1_tarski(B_63, k1_relat_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.49  tff(c_218, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_123, c_200])).
% 3.24/1.49  tff(c_225, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_62, c_218])).
% 3.24/1.49  tff(c_228, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_225])).
% 3.24/1.49  tff(c_265, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_228])).
% 3.24/1.49  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_265])).
% 3.24/1.49  tff(c_270, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_1'), inference(splitRight, [status(thm)], [c_225])).
% 3.24/1.49  tff(c_24, plain, (![A_10, B_12]: (k9_relat_1(k2_funct_1(A_10), k9_relat_1(A_10, B_12))=B_12 | ~r1_tarski(B_12, k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.49  tff(c_278, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_1')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_24])).
% 3.24/1.49  tff(c_359, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_278])).
% 3.24/1.49  tff(c_362, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_359])).
% 3.24/1.49  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_362])).
% 3.24/1.49  tff(c_368, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_278])).
% 3.24/1.49  tff(c_14, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.49  tff(c_28, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.24/1.49  tff(c_367, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_1')=k2_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_278])).
% 3.24/1.49  tff(c_498, plain, (~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_367])).
% 3.24/1.49  tff(c_501, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_498])).
% 3.24/1.49  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_62, c_6, c_501])).
% 3.24/1.49  tff(c_505, plain, (~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_1')=k2_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_367])).
% 3.24/1.49  tff(c_548, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_505])).
% 3.24/1.49  tff(c_551, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_548])).
% 3.24/1.49  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_551])).
% 3.24/1.49  tff(c_557, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_505])).
% 3.24/1.49  tff(c_18, plain, (![A_9]: (v2_funct_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.49  tff(c_556, plain, (~v2_funct_1(k2_funct_1('#skF_4')) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_1')=k2_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_505])).
% 3.24/1.49  tff(c_558, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_556])).
% 3.24/1.49  tff(c_561, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_558])).
% 3.24/1.49  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_62, c_561])).
% 3.24/1.49  tff(c_567, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_556])).
% 3.24/1.49  tff(c_172, plain, (![A_51]: (k1_relat_1(k2_funct_1(A_51))=k2_relat_1(A_51) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.24/1.49  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.49  tff(c_436, plain, (![A_83]: (k9_relat_1(k2_funct_1(A_83), k2_relat_1(A_83))=k2_relat_1(k2_funct_1(A_83)) | ~v1_relat_1(k2_funct_1(A_83)) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_172, c_8])).
% 3.24/1.49  tff(c_445, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_436, c_270])).
% 3.24/1.49  tff(c_469, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_62, c_368, c_445])).
% 3.24/1.49  tff(c_34, plain, (![A_16]: (k2_funct_1(k2_funct_1(A_16))=A_16 | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.24/1.49  tff(c_322, plain, (![B_72, A_73]: (k1_funct_1(B_72, k1_funct_1(k2_funct_1(B_72), A_73))=A_73 | ~r2_hidden(A_73, k2_relat_1(B_72)) | ~v2_funct_1(B_72) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.24/1.49  tff(c_820, plain, (![A_89, A_90]: (k1_funct_1(k2_funct_1(A_89), k1_funct_1(A_89, A_90))=A_90 | ~r2_hidden(A_90, k2_relat_1(k2_funct_1(A_89))) | ~v2_funct_1(k2_funct_1(A_89)) | ~v1_funct_1(k2_funct_1(A_89)) | ~v1_relat_1(k2_funct_1(A_89)) | ~v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_34, c_322])).
% 3.24/1.49  tff(c_824, plain, (![A_90]: (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', A_90))=A_90 | ~r2_hidden(A_90, '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_469, c_820])).
% 3.24/1.49  tff(c_852, plain, (![A_91]: (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', A_91))=A_91 | ~r2_hidden(A_91, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68, c_62, c_368, c_557, c_567, c_824])).
% 3.24/1.49  tff(c_56, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.24/1.49  tff(c_861, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_852, c_56])).
% 3.24/1.49  tff(c_876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_861])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 180
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 11
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Subsume      : 6
% 3.24/1.49  #Demod        : 276
% 3.24/1.49  #Tautology    : 108
% 3.24/1.49  #SimpNegUnit  : 4
% 3.24/1.49  #BackRed      : 10
% 3.24/1.49  
% 3.24/1.49  #Partial instantiations: 0
% 3.24/1.49  #Strategies tried      : 1
% 3.24/1.49  
% 3.24/1.49  Timing (in seconds)
% 3.24/1.49  ----------------------
% 3.24/1.49  Preprocessing        : 0.35
% 3.24/1.49  Parsing              : 0.18
% 3.24/1.49  CNF conversion       : 0.02
% 3.24/1.49  Main loop            : 0.38
% 3.24/1.49  Inferencing          : 0.13
% 3.24/1.49  Reduction            : 0.12
% 3.24/1.49  Demodulation         : 0.09
% 3.24/1.49  BG Simplification    : 0.02
% 3.24/1.49  Subsumption          : 0.08
% 3.24/1.49  Abstraction          : 0.02
% 3.24/1.49  MUC search           : 0.00
% 3.24/1.49  Cooper               : 0.00
% 3.24/1.49  Total                : 0.76
% 3.24/1.49  Index Insertion      : 0.00
% 3.24/1.49  Index Deletion       : 0.00
% 3.24/1.49  Index Matching       : 0.00
% 3.24/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
