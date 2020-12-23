%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:27 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 205 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 634 expanded)
%              Number of equality atoms :   20 (  90 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_72,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(c_46,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_26])).

tff(c_342,plain,(
    ! [A_82,B_87,F_85,E_84,D_86,C_83] :
      ( m1_subset_1(k1_partfun1(A_82,B_87,C_83,D_86,E_84,F_85),k1_zfmisc_1(k2_zfmisc_1(A_82,D_86)))
      | ~ m1_subset_1(F_85,k1_zfmisc_1(k2_zfmisc_1(C_83,D_86)))
      | ~ v1_funct_1(F_85)
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_87)))
      | ~ v1_funct_1(E_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_253,plain,(
    ! [D_62,C_63,A_64,B_65] :
      ( D_62 = C_63
      | ~ r2_relset_1(A_64,B_65,C_63,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_259,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_253])).

tff(c_270,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_259])).

tff(c_289,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_350,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_342,c_289])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_50,c_350])).

tff(c_368,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_565,plain,(
    ! [C_147,D_144,E_148,A_146,B_145] :
      ( k1_xboole_0 = C_147
      | v2_funct_1(D_144)
      | ~ v2_funct_1(k1_partfun1(A_146,B_145,B_145,C_147,D_144,E_148))
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(B_145,C_147)))
      | ~ v1_funct_2(E_148,B_145,C_147)
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145)))
      | ~ v1_funct_2(D_144,A_146,B_145)
      | ~ v1_funct_1(D_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_567,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_565])).

tff(c_572,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_52,c_50,c_63,c_567])).

tff(c_573,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_572])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_107,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_113,plain,(
    ! [B_43,A_44] :
      ( v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_107,c_113])).

tff(c_130,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [B_49,A_50] :
      ( ~ r1_xboole_0(B_49,A_50)
      | ~ r1_tarski(B_49,A_50)
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [A_51] :
      ( ~ r1_tarski(A_51,k1_xboole_0)
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_161])).

tff(c_170,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_166])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_170])).

tff(c_176,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_596,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_176])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_600,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_573,c_12])).

tff(c_128,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_196,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_654,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_196])).

tff(c_658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_654])).

tff(c_659,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_669,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_659,c_16])).

tff(c_712,plain,(
    ! [A_163] :
      ( v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | ~ v1_xboole_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_715,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_712,c_46])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_669,c_62,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.15/1.46  
% 3.15/1.46  %Foreground sorts:
% 3.15/1.46  
% 3.15/1.46  
% 3.15/1.46  %Background operators:
% 3.15/1.46  
% 3.15/1.46  
% 3.15/1.46  %Foreground operators:
% 3.15/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.15/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.46  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.15/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.46  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.46  
% 3.31/1.47  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 3.31/1.47  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.31/1.47  tff(f_72, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 3.31/1.47  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.31/1.47  tff(f_96, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.31/1.47  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.31/1.47  tff(f_120, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.31/1.47  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.31/1.47  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.31/1.47  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.31/1.47  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.31/1.47  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.31/1.47  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.31/1.47  tff(f_70, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.31/1.47  tff(c_46, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_40, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.31/1.47  tff(c_26, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.47  tff(c_63, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_26])).
% 3.31/1.47  tff(c_342, plain, (![A_82, B_87, F_85, E_84, D_86, C_83]: (m1_subset_1(k1_partfun1(A_82, B_87, C_83, D_86, E_84, F_85), k1_zfmisc_1(k2_zfmisc_1(A_82, D_86))) | ~m1_subset_1(F_85, k1_zfmisc_1(k2_zfmisc_1(C_83, D_86))) | ~v1_funct_1(F_85) | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_87))) | ~v1_funct_1(E_84))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.31/1.47  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.31/1.47  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.31/1.47  tff(c_253, plain, (![D_62, C_63, A_64, B_65]: (D_62=C_63 | ~r2_relset_1(A_64, B_65, C_63, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.47  tff(c_259, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_253])).
% 3.31/1.47  tff(c_270, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_259])).
% 3.31/1.47  tff(c_289, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_270])).
% 3.31/1.48  tff(c_350, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_342, c_289])).
% 3.31/1.48  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_50, c_350])).
% 3.31/1.48  tff(c_368, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_270])).
% 3.31/1.48  tff(c_565, plain, (![C_147, D_144, E_148, A_146, B_145]: (k1_xboole_0=C_147 | v2_funct_1(D_144) | ~v2_funct_1(k1_partfun1(A_146, B_145, B_145, C_147, D_144, E_148)) | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(B_145, C_147))) | ~v1_funct_2(E_148, B_145, C_147) | ~v1_funct_1(E_148) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))) | ~v1_funct_2(D_144, A_146, B_145) | ~v1_funct_1(D_144))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.31/1.48  tff(c_567, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_368, c_565])).
% 3.31/1.48  tff(c_572, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_52, c_50, c_63, c_567])).
% 3.31/1.48  tff(c_573, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_46, c_572])).
% 3.31/1.48  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.48  tff(c_103, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.31/1.48  tff(c_107, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 3.31/1.48  tff(c_113, plain, (![B_43, A_44]: (v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.48  tff(c_126, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_113])).
% 3.31/1.48  tff(c_130, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_126])).
% 3.31/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.48  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.48  tff(c_161, plain, (![B_49, A_50]: (~r1_xboole_0(B_49, A_50) | ~r1_tarski(B_49, A_50) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.48  tff(c_166, plain, (![A_51]: (~r1_tarski(A_51, k1_xboole_0) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_4, c_161])).
% 3.31/1.48  tff(c_170, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_166])).
% 3.31/1.48  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_170])).
% 3.31/1.48  tff(c_176, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 3.31/1.48  tff(c_596, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_176])).
% 3.31/1.48  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.48  tff(c_600, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_573, c_12])).
% 3.31/1.48  tff(c_128, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_113])).
% 3.31/1.48  tff(c_196, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_128])).
% 3.31/1.48  tff(c_654, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_196])).
% 3.31/1.48  tff(c_658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_596, c_654])).
% 3.31/1.48  tff(c_659, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_128])).
% 3.31/1.48  tff(c_16, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.48  tff(c_669, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_659, c_16])).
% 3.31/1.48  tff(c_712, plain, (![A_163]: (v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | ~v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.31/1.48  tff(c_715, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_712, c_46])).
% 3.31/1.48  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_659, c_669, c_62, c_715])).
% 3.31/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.48  
% 3.31/1.48  Inference rules
% 3.31/1.48  ----------------------
% 3.31/1.48  #Ref     : 0
% 3.31/1.48  #Sup     : 130
% 3.31/1.48  #Fact    : 0
% 3.31/1.48  #Define  : 0
% 3.31/1.48  #Split   : 9
% 3.31/1.48  #Chain   : 0
% 3.31/1.48  #Close   : 0
% 3.31/1.48  
% 3.31/1.48  Ordering : KBO
% 3.31/1.48  
% 3.31/1.48  Simplification rules
% 3.31/1.48  ----------------------
% 3.31/1.48  #Subsume      : 2
% 3.31/1.48  #Demod        : 139
% 3.31/1.48  #Tautology    : 40
% 3.31/1.48  #SimpNegUnit  : 2
% 3.31/1.48  #BackRed      : 32
% 3.31/1.48  
% 3.31/1.48  #Partial instantiations: 0
% 3.31/1.48  #Strategies tried      : 1
% 3.31/1.48  
% 3.31/1.48  Timing (in seconds)
% 3.31/1.48  ----------------------
% 3.31/1.48  Preprocessing        : 0.33
% 3.31/1.48  Parsing              : 0.18
% 3.31/1.48  CNF conversion       : 0.02
% 3.31/1.48  Main loop            : 0.37
% 3.31/1.48  Inferencing          : 0.13
% 3.31/1.48  Reduction            : 0.13
% 3.31/1.48  Demodulation         : 0.09
% 3.31/1.48  BG Simplification    : 0.02
% 3.31/1.48  Subsumption          : 0.06
% 3.31/1.48  Abstraction          : 0.01
% 3.31/1.48  MUC search           : 0.00
% 3.31/1.48  Cooper               : 0.00
% 3.31/1.48  Total                : 0.74
% 3.31/1.48  Index Insertion      : 0.00
% 3.31/1.48  Index Deletion       : 0.00
% 3.31/1.48  Index Matching       : 0.00
% 3.31/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
