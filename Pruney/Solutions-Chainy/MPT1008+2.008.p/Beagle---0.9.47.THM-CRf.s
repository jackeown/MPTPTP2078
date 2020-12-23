%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 21.52s
% Output     : CNFRefutation 21.52s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 213 expanded)
%              Number of leaves         :   54 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  194 ( 423 expanded)
%              Number of equality atoms :   74 ( 146 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_148,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_90,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_29523,plain,(
    ! [A_81528,B_81529,C_81530] :
      ( r2_hidden('#skF_3'(A_81528,B_81529,C_81530),B_81529)
      | k1_relset_1(B_81529,A_81528,C_81530) = B_81529
      | ~ m1_subset_1(C_81530,k1_zfmisc_1(k2_zfmisc_1(B_81529,A_81528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_29536,plain,
    ( r2_hidden('#skF_3'('#skF_6',k1_tarski('#skF_5'),'#skF_7'),k1_tarski('#skF_5'))
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_29523])).

tff(c_67330,plain,(
    k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_29536])).

tff(c_143,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_157,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_143])).

tff(c_54,plain,(
    ! [A_30] :
      ( k2_relat_1(A_30) != k1_xboole_0
      | k1_xboole_0 = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_164,plain,
    ( k2_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_157,c_54])).

tff(c_166,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_443,plain,(
    ! [A_139,B_140] :
      ( k9_relat_1(A_139,k1_tarski(B_140)) = k11_relat_1(A_139,B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_297,plain,(
    ! [C_114,A_115,B_116] :
      ( v4_relat_1(C_114,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_311,plain,(
    v4_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_297])).

tff(c_52,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = B_29
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_314,plain,
    ( k7_relat_1('#skF_7',k1_tarski('#skF_5')) = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_311,c_52])).

tff(c_317,plain,(
    k7_relat_1('#skF_7',k1_tarski('#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_314])).

tff(c_46,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_46])).

tff(c_325,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_321])).

tff(c_449,plain,
    ( k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_325])).

tff(c_458,plain,(
    k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_449])).

tff(c_48,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,k1_relat_1(B_27))
      | k11_relat_1(B_27,A_26) = k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_94,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_577,plain,(
    ! [B_173,A_174] :
      ( k1_tarski(k1_funct_1(B_173,A_174)) = k2_relat_1(B_173)
      | k1_tarski(A_174) != k1_relat_1(B_173)
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_528,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_542,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_528])).

tff(c_86,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') != k1_tarski(k1_funct_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_543,plain,(
    k1_tarski(k1_funct_1('#skF_7','#skF_5')) != k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_86])).

tff(c_586,plain,
    ( k1_tarski('#skF_5') != k1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_543])).

tff(c_612,plain,(
    k1_tarski('#skF_5') != k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_94,c_586])).

tff(c_137,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k1_tarski(A_73),k1_zfmisc_1(B_74))
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_tarski(A_73),B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_137,c_34])).

tff(c_388,plain,(
    ! [B_129,A_130] :
      ( r1_tarski(k1_relat_1(B_129),A_130)
      | ~ v4_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_765,plain,(
    ! [B_215,A_216] :
      ( k1_relat_1(B_215) = A_216
      | ~ r1_tarski(A_216,k1_relat_1(B_215))
      | ~ v4_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(resolution,[status(thm)],[c_388,c_4])).

tff(c_970,plain,(
    ! [A_262,B_263] :
      ( k1_tarski(A_262) = k1_relat_1(B_263)
      | ~ v4_relat_1(B_263,k1_tarski(A_262))
      | ~ v1_relat_1(B_263)
      | ~ r2_hidden(A_262,k1_relat_1(B_263)) ) ),
    inference(resolution,[status(thm)],[c_141,c_765])).

tff(c_988,plain,
    ( k1_tarski('#skF_5') = k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_311,c_970])).

tff(c_1000,plain,
    ( k1_tarski('#skF_5') = k1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_988])).

tff(c_1001,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_1000])).

tff(c_1004,plain,
    ( k11_relat_1('#skF_7','#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1001])).

tff(c_1007,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_458,c_1004])).

tff(c_1009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_1007])).

tff(c_1010,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1014,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_2])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ! [D_60,B_61] : r2_hidden(D_60,k2_tarski(D_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_106])).

tff(c_101780,plain,(
    ! [D_299875,A_299876,B_299877,C_299878] :
      ( r2_hidden(k4_tarski(D_299875,'#skF_4'(A_299876,B_299877,C_299878,D_299875)),C_299878)
      | ~ r2_hidden(D_299875,B_299877)
      | k1_relset_1(B_299877,A_299876,C_299878) != B_299877
      | ~ m1_subset_1(C_299878,k1_zfmisc_1(k2_zfmisc_1(B_299877,A_299876))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1116,plain,(
    ! [C_286,B_287,A_288] :
      ( ~ v1_xboole_0(C_286)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(C_286))
      | ~ r2_hidden(A_288,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1126,plain,(
    ! [B_289,A_290,A_291] :
      ( ~ v1_xboole_0(B_289)
      | ~ r2_hidden(A_290,A_291)
      | ~ r1_tarski(A_291,B_289) ) ),
    inference(resolution,[status(thm)],[c_36,c_1116])).

tff(c_1141,plain,(
    ! [B_294,A_295] :
      ( ~ v1_xboole_0(B_294)
      | ~ r1_tarski(k1_tarski(A_295),B_294) ) ),
    inference(resolution,[status(thm)],[c_109,c_1126])).

tff(c_1149,plain,(
    ! [B_74,A_73] :
      ( ~ v1_xboole_0(B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_141,c_1141])).

tff(c_126717,plain,(
    ! [C_336483,D_336484,B_336485,A_336486] :
      ( ~ v1_xboole_0(C_336483)
      | ~ r2_hidden(D_336484,B_336485)
      | k1_relset_1(B_336485,A_336486,C_336483) != B_336485
      | ~ m1_subset_1(C_336483,k1_zfmisc_1(k2_zfmisc_1(B_336485,A_336486))) ) ),
    inference(resolution,[status(thm)],[c_101780,c_1149])).

tff(c_126781,plain,(
    ! [C_336607,A_336608,A_336609] :
      ( ~ v1_xboole_0(C_336607)
      | k1_relset_1(k1_tarski(A_336608),A_336609,C_336607) != k1_tarski(A_336608)
      | ~ m1_subset_1(C_336607,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_336608),A_336609))) ) ),
    inference(resolution,[status(thm)],[c_109,c_126717])).

tff(c_126822,plain,
    ( ~ v1_xboole_0('#skF_7')
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') != k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_126781])).

tff(c_126828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67330,c_1014,c_126822])).

tff(c_126830,plain,(
    k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') != k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_29536])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1015,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_88])).

tff(c_92,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_84,plain,(
    ! [B_56,A_55,C_57] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_55,B_56,C_57) = A_55
      | ~ v1_funct_2(C_57,A_55,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_126867,plain,(
    ! [B_336732,A_336733,C_336734] :
      ( B_336732 = '#skF_7'
      | k1_relset_1(A_336733,B_336732,C_336734) = A_336733
      | ~ v1_funct_2(C_336734,A_336733,B_336732)
      | ~ m1_subset_1(C_336734,k1_zfmisc_1(k2_zfmisc_1(A_336733,B_336732))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_84])).

tff(c_126881,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5')
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_126867])).

tff(c_126886,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126881])).

tff(c_126888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126830,c_1015,c_126886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:43:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.52/12.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.52/12.08  
% 21.52/12.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.52/12.08  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 21.52/12.08  
% 21.52/12.08  %Foreground sorts:
% 21.52/12.08  
% 21.52/12.08  
% 21.52/12.08  %Background operators:
% 21.52/12.08  
% 21.52/12.08  
% 21.52/12.08  %Foreground operators:
% 21.52/12.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 21.52/12.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 21.52/12.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.52/12.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.52/12.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.52/12.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.52/12.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.52/12.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 21.52/12.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.52/12.08  tff('#skF_7', type, '#skF_7': $i).
% 21.52/12.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.52/12.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.52/12.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.52/12.08  tff('#skF_5', type, '#skF_5': $i).
% 21.52/12.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.52/12.08  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 21.52/12.08  tff('#skF_6', type, '#skF_6': $i).
% 21.52/12.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.52/12.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 21.52/12.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 21.52/12.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 21.52/12.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.52/12.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.52/12.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 21.52/12.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 21.52/12.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.52/12.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.52/12.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.52/12.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 21.52/12.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.52/12.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.52/12.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.52/12.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.52/12.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.52/12.08  
% 21.52/12.10  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 21.52/12.10  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 21.52/12.10  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 21.52/12.10  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 21.52/12.10  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 21.52/12.10  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.52/12.10  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 21.52/12.10  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 21.52/12.10  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 21.52/12.10  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 21.52/12.10  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 21.52/12.10  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 21.52/12.10  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.52/12.10  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 21.52/12.10  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.52/12.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 21.52/12.10  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 21.52/12.10  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 21.52/12.10  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 21.52/12.10  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 21.52/12.10  tff(c_90, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 21.52/12.10  tff(c_29523, plain, (![A_81528, B_81529, C_81530]: (r2_hidden('#skF_3'(A_81528, B_81529, C_81530), B_81529) | k1_relset_1(B_81529, A_81528, C_81530)=B_81529 | ~m1_subset_1(C_81530, k1_zfmisc_1(k2_zfmisc_1(B_81529, A_81528))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 21.52/12.10  tff(c_29536, plain, (r2_hidden('#skF_3'('#skF_6', k1_tarski('#skF_5'), '#skF_7'), k1_tarski('#skF_5')) | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_90, c_29523])).
% 21.52/12.10  tff(c_67330, plain, (k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_29536])).
% 21.52/12.10  tff(c_143, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.52/12.10  tff(c_157, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_143])).
% 21.52/12.10  tff(c_54, plain, (![A_30]: (k2_relat_1(A_30)!=k1_xboole_0 | k1_xboole_0=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.52/12.10  tff(c_164, plain, (k2_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_157, c_54])).
% 21.52/12.10  tff(c_166, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_164])).
% 21.52/12.10  tff(c_443, plain, (![A_139, B_140]: (k9_relat_1(A_139, k1_tarski(B_140))=k11_relat_1(A_139, B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.52/12.10  tff(c_297, plain, (![C_114, A_115, B_116]: (v4_relat_1(C_114, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 21.52/12.10  tff(c_311, plain, (v4_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_297])).
% 21.52/12.10  tff(c_52, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=B_29 | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 21.52/12.10  tff(c_314, plain, (k7_relat_1('#skF_7', k1_tarski('#skF_5'))='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_311, c_52])).
% 21.52/12.10  tff(c_317, plain, (k7_relat_1('#skF_7', k1_tarski('#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_314])).
% 21.52/12.10  tff(c_46, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.52/12.10  tff(c_321, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_317, c_46])).
% 21.52/12.10  tff(c_325, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_321])).
% 21.52/12.10  tff(c_449, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_443, c_325])).
% 21.52/12.10  tff(c_458, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_449])).
% 21.52/12.10  tff(c_48, plain, (![A_26, B_27]: (r2_hidden(A_26, k1_relat_1(B_27)) | k11_relat_1(B_27, A_26)=k1_xboole_0 | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 21.52/12.10  tff(c_94, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_160])).
% 21.52/12.10  tff(c_577, plain, (![B_173, A_174]: (k1_tarski(k1_funct_1(B_173, A_174))=k2_relat_1(B_173) | k1_tarski(A_174)!=k1_relat_1(B_173) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_104])).
% 21.52/12.10  tff(c_528, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.52/12.10  tff(c_542, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_528])).
% 21.52/12.10  tff(c_86, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')!=k1_tarski(k1_funct_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 21.52/12.10  tff(c_543, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))!=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_86])).
% 21.52/12.10  tff(c_586, plain, (k1_tarski('#skF_5')!=k1_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_577, c_543])).
% 21.52/12.10  tff(c_612, plain, (k1_tarski('#skF_5')!=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_94, c_586])).
% 21.52/12.10  tff(c_137, plain, (![A_73, B_74]: (m1_subset_1(k1_tarski(A_73), k1_zfmisc_1(B_74)) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.52/12.10  tff(c_34, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.52/12.10  tff(c_141, plain, (![A_73, B_74]: (r1_tarski(k1_tarski(A_73), B_74) | ~r2_hidden(A_73, B_74))), inference(resolution, [status(thm)], [c_137, c_34])).
% 21.52/12.10  tff(c_388, plain, (![B_129, A_130]: (r1_tarski(k1_relat_1(B_129), A_130) | ~v4_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.52/12.10  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.52/12.10  tff(c_765, plain, (![B_215, A_216]: (k1_relat_1(B_215)=A_216 | ~r1_tarski(A_216, k1_relat_1(B_215)) | ~v4_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(resolution, [status(thm)], [c_388, c_4])).
% 21.52/12.10  tff(c_970, plain, (![A_262, B_263]: (k1_tarski(A_262)=k1_relat_1(B_263) | ~v4_relat_1(B_263, k1_tarski(A_262)) | ~v1_relat_1(B_263) | ~r2_hidden(A_262, k1_relat_1(B_263)))), inference(resolution, [status(thm)], [c_141, c_765])).
% 21.52/12.10  tff(c_988, plain, (k1_tarski('#skF_5')=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_311, c_970])).
% 21.52/12.10  tff(c_1000, plain, (k1_tarski('#skF_5')=k1_relat_1('#skF_7') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_988])).
% 21.52/12.10  tff(c_1001, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_612, c_1000])).
% 21.52/12.10  tff(c_1004, plain, (k11_relat_1('#skF_7', '#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1001])).
% 21.52/12.10  tff(c_1007, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_458, c_1004])).
% 21.52/12.10  tff(c_1009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_1007])).
% 21.52/12.10  tff(c_1010, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_164])).
% 21.52/12.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 21.52/12.10  tff(c_1014, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_2])).
% 21.52/12.10  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.52/12.10  tff(c_106, plain, (![D_60, B_61]: (r2_hidden(D_60, k2_tarski(D_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.52/12.10  tff(c_109, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_106])).
% 21.52/12.10  tff(c_101780, plain, (![D_299875, A_299876, B_299877, C_299878]: (r2_hidden(k4_tarski(D_299875, '#skF_4'(A_299876, B_299877, C_299878, D_299875)), C_299878) | ~r2_hidden(D_299875, B_299877) | k1_relset_1(B_299877, A_299876, C_299878)!=B_299877 | ~m1_subset_1(C_299878, k1_zfmisc_1(k2_zfmisc_1(B_299877, A_299876))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 21.52/12.10  tff(c_36, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.52/12.10  tff(c_1116, plain, (![C_286, B_287, A_288]: (~v1_xboole_0(C_286) | ~m1_subset_1(B_287, k1_zfmisc_1(C_286)) | ~r2_hidden(A_288, B_287))), inference(cnfTransformation, [status(thm)], [f_60])).
% 21.52/12.10  tff(c_1126, plain, (![B_289, A_290, A_291]: (~v1_xboole_0(B_289) | ~r2_hidden(A_290, A_291) | ~r1_tarski(A_291, B_289))), inference(resolution, [status(thm)], [c_36, c_1116])).
% 21.52/12.10  tff(c_1141, plain, (![B_294, A_295]: (~v1_xboole_0(B_294) | ~r1_tarski(k1_tarski(A_295), B_294))), inference(resolution, [status(thm)], [c_109, c_1126])).
% 21.52/12.10  tff(c_1149, plain, (![B_74, A_73]: (~v1_xboole_0(B_74) | ~r2_hidden(A_73, B_74))), inference(resolution, [status(thm)], [c_141, c_1141])).
% 21.52/12.10  tff(c_126717, plain, (![C_336483, D_336484, B_336485, A_336486]: (~v1_xboole_0(C_336483) | ~r2_hidden(D_336484, B_336485) | k1_relset_1(B_336485, A_336486, C_336483)!=B_336485 | ~m1_subset_1(C_336483, k1_zfmisc_1(k2_zfmisc_1(B_336485, A_336486))))), inference(resolution, [status(thm)], [c_101780, c_1149])).
% 21.52/12.10  tff(c_126781, plain, (![C_336607, A_336608, A_336609]: (~v1_xboole_0(C_336607) | k1_relset_1(k1_tarski(A_336608), A_336609, C_336607)!=k1_tarski(A_336608) | ~m1_subset_1(C_336607, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_336608), A_336609))))), inference(resolution, [status(thm)], [c_109, c_126717])).
% 21.52/12.10  tff(c_126822, plain, (~v1_xboole_0('#skF_7') | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')!=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_90, c_126781])).
% 21.52/12.10  tff(c_126828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67330, c_1014, c_126822])).
% 21.52/12.10  tff(c_126830, plain, (k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')!=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_29536])).
% 21.52/12.10  tff(c_88, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_160])).
% 21.52/12.10  tff(c_1015, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_88])).
% 21.52/12.10  tff(c_92, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 21.52/12.10  tff(c_84, plain, (![B_56, A_55, C_57]: (k1_xboole_0=B_56 | k1_relset_1(A_55, B_56, C_57)=A_55 | ~v1_funct_2(C_57, A_55, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 21.52/12.10  tff(c_126867, plain, (![B_336732, A_336733, C_336734]: (B_336732='#skF_7' | k1_relset_1(A_336733, B_336732, C_336734)=A_336733 | ~v1_funct_2(C_336734, A_336733, B_336732) | ~m1_subset_1(C_336734, k1_zfmisc_1(k2_zfmisc_1(A_336733, B_336732))))), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_84])).
% 21.52/12.10  tff(c_126881, plain, ('#skF_7'='#skF_6' | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5') | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_90, c_126867])).
% 21.52/12.10  tff(c_126886, plain, ('#skF_7'='#skF_6' | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_126881])).
% 21.52/12.10  tff(c_126888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126830, c_1015, c_126886])).
% 21.52/12.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.52/12.10  
% 21.52/12.10  Inference rules
% 21.52/12.10  ----------------------
% 21.52/12.10  #Ref     : 21
% 21.52/12.10  #Sup     : 16586
% 21.52/12.10  #Fact    : 320
% 21.52/12.10  #Define  : 0
% 21.52/12.10  #Split   : 116
% 21.52/12.10  #Chain   : 0
% 21.52/12.10  #Close   : 0
% 21.52/12.10  
% 21.52/12.10  Ordering : KBO
% 21.52/12.10  
% 21.52/12.10  Simplification rules
% 21.52/12.10  ----------------------
% 21.52/12.10  #Subsume      : 6514
% 21.52/12.10  #Demod        : 4875
% 21.52/12.10  #Tautology    : 3911
% 21.52/12.10  #SimpNegUnit  : 585
% 21.52/12.10  #BackRed      : 34
% 21.52/12.10  
% 21.52/12.10  #Partial instantiations: 183194
% 21.52/12.10  #Strategies tried      : 1
% 21.52/12.10  
% 21.52/12.10  Timing (in seconds)
% 21.52/12.10  ----------------------
% 21.52/12.10  Preprocessing        : 0.38
% 21.52/12.10  Parsing              : 0.20
% 21.52/12.10  CNF conversion       : 0.03
% 21.52/12.10  Main loop            : 10.93
% 21.52/12.10  Inferencing          : 5.08
% 21.52/12.10  Reduction            : 2.84
% 21.52/12.10  Demodulation         : 2.01
% 21.52/12.10  BG Simplification    : 0.32
% 21.52/12.10  Subsumption          : 2.09
% 21.52/12.10  Abstraction          : 0.48
% 21.52/12.10  MUC search           : 0.00
% 21.52/12.10  Cooper               : 0.00
% 21.52/12.10  Total                : 11.35
% 21.52/12.10  Index Insertion      : 0.00
% 21.52/12.10  Index Deletion       : 0.00
% 21.52/12.10  Index Matching       : 0.00
% 21.52/12.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
