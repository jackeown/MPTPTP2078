%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:02 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 187 expanded)
%              Number of leaves         :   44 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 374 expanded)
%              Number of equality atoms :   78 ( 133 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_89,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_42,plain,(
    ! [A_39,B_40] : v1_relat_1(k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_152,plain,(
    ! [B_84,A_85] :
      ( v1_relat_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_155,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_158,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_155])).

tff(c_44,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k9_relat_1(B_42,A_41),k2_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) != k1_xboole_0
      | k1_xboole_0 = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_165,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_158,c_50])).

tff(c_167,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_255,plain,(
    ! [B_126,A_127] :
      ( k1_tarski(k1_funct_1(B_126,A_127)) = k2_relat_1(B_126)
      | k1_tarski(A_127) != k1_relat_1(B_126)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_241,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_relset_1(A_121,B_122,C_123,D_124) = k9_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_244,plain,(
    ! [D_124] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_124) = k9_relat_1('#skF_4',D_124) ),
    inference(resolution,[status(thm)],[c_64,c_241])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_245,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_60])).

tff(c_261,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_245])).

tff(c_288,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_68,c_261])).

tff(c_290,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_187,plain,(
    ! [C_92,A_93,B_94] :
      ( v4_relat_1(C_92,A_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_191,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_187])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k1_relat_1(B_38),A_37)
      | ~ v4_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_332,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k1_enumset1(A_155,B_156,C_157) = D_158
      | k2_tarski(A_155,C_157) = D_158
      | k2_tarski(B_156,C_157) = D_158
      | k2_tarski(A_155,B_156) = D_158
      | k1_tarski(C_157) = D_158
      | k1_tarski(B_156) = D_158
      | k1_tarski(A_155) = D_158
      | k1_xboole_0 = D_158
      | ~ r1_tarski(D_158,k1_enumset1(A_155,B_156,C_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_354,plain,(
    ! [A_3,B_4,D_158] :
      ( k1_enumset1(A_3,A_3,B_4) = D_158
      | k2_tarski(A_3,B_4) = D_158
      | k2_tarski(A_3,B_4) = D_158
      | k2_tarski(A_3,A_3) = D_158
      | k1_tarski(B_4) = D_158
      | k1_tarski(A_3) = D_158
      | k1_tarski(A_3) = D_158
      | k1_xboole_0 = D_158
      | ~ r1_tarski(D_158,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_332])).

tff(c_408,plain,(
    ! [A_169,B_170,D_171] :
      ( k2_tarski(A_169,B_170) = D_171
      | k2_tarski(A_169,B_170) = D_171
      | k2_tarski(A_169,B_170) = D_171
      | k1_tarski(A_169) = D_171
      | k1_tarski(B_170) = D_171
      | k1_tarski(A_169) = D_171
      | k1_tarski(A_169) = D_171
      | k1_xboole_0 = D_171
      | ~ r1_tarski(D_171,k2_tarski(A_169,B_170)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_354])).

tff(c_447,plain,(
    ! [A_172,B_173,B_174] :
      ( k2_tarski(A_172,B_173) = k1_relat_1(B_174)
      | k1_tarski(B_173) = k1_relat_1(B_174)
      | k1_tarski(A_172) = k1_relat_1(B_174)
      | k1_relat_1(B_174) = k1_xboole_0
      | ~ v4_relat_1(B_174,k2_tarski(A_172,B_173))
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_40,c_408])).

tff(c_450,plain,(
    ! [A_2,B_174] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_174)
      | k1_tarski(A_2) = k1_relat_1(B_174)
      | k1_tarski(A_2) = k1_relat_1(B_174)
      | k1_relat_1(B_174) = k1_xboole_0
      | ~ v4_relat_1(B_174,k1_tarski(A_2))
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_447])).

tff(c_452,plain,(
    ! [A_175,B_176] :
      ( k1_tarski(A_175) = k1_relat_1(B_176)
      | k1_tarski(A_175) = k1_relat_1(B_176)
      | k1_tarski(A_175) = k1_relat_1(B_176)
      | k1_relat_1(B_176) = k1_xboole_0
      | ~ v4_relat_1(B_176,k1_tarski(A_175))
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_450])).

tff(c_458,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_191,c_452])).

tff(c_461,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_458])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_290,c_461])).

tff(c_464,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_534,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_464])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_534])).

tff(c_539,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_544,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_2])).

tff(c_46,plain,(
    ! [A_43] : k9_relat_1(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_543,plain,(
    ! [A_43] : k9_relat_1('#skF_4',A_43) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_539,c_46])).

tff(c_713,plain,(
    ! [A_225,B_226,C_227,D_228] :
      ( k7_relset_1(A_225,B_226,C_227,D_228) = k9_relat_1(C_227,D_228)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_715,plain,(
    ! [D_228] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_228) = k9_relat_1('#skF_4',D_228) ),
    inference(resolution,[status(thm)],[c_64,c_713])).

tff(c_717,plain,(
    ! [D_228] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_228) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_715])).

tff(c_718,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_60])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.48  
% 3.03/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.03/1.49  
% 3.03/1.49  %Foreground sorts:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Background operators:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Foreground operators:
% 3.03/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.03/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.03/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.03/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.03/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.03/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.03/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.49  
% 3.03/1.50  tff(f_83, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.03/1.50  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.03/1.50  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.03/1.50  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.03/1.50  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.03/1.50  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.03/1.50  tff(f_115, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.03/1.50  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.03/1.50  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.03/1.50  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.03/1.50  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.03/1.50  tff(f_68, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.03/1.50  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.03/1.50  tff(f_89, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.03/1.50  tff(c_42, plain, (![A_39, B_40]: (v1_relat_1(k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.50  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.03/1.50  tff(c_152, plain, (![B_84, A_85]: (v1_relat_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.50  tff(c_155, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_152])).
% 3.03/1.50  tff(c_158, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_155])).
% 3.03/1.50  tff(c_44, plain, (![B_42, A_41]: (r1_tarski(k9_relat_1(B_42, A_41), k2_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.50  tff(c_50, plain, (![A_44]: (k1_relat_1(A_44)!=k1_xboole_0 | k1_xboole_0=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.03/1.50  tff(c_165, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_158, c_50])).
% 3.03/1.50  tff(c_167, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_165])).
% 3.03/1.50  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.03/1.50  tff(c_255, plain, (![B_126, A_127]: (k1_tarski(k1_funct_1(B_126, A_127))=k2_relat_1(B_126) | k1_tarski(A_127)!=k1_relat_1(B_126) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.03/1.50  tff(c_241, plain, (![A_121, B_122, C_123, D_124]: (k7_relset_1(A_121, B_122, C_123, D_124)=k9_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.03/1.50  tff(c_244, plain, (![D_124]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_124)=k9_relat_1('#skF_4', D_124))), inference(resolution, [status(thm)], [c_64, c_241])).
% 3.03/1.50  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.03/1.50  tff(c_245, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_60])).
% 3.03/1.50  tff(c_261, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_255, c_245])).
% 3.03/1.50  tff(c_288, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_68, c_261])).
% 3.03/1.50  tff(c_290, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_288])).
% 3.03/1.50  tff(c_187, plain, (![C_92, A_93, B_94]: (v4_relat_1(C_92, A_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.03/1.50  tff(c_191, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_187])).
% 3.03/1.50  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.50  tff(c_40, plain, (![B_38, A_37]: (r1_tarski(k1_relat_1(B_38), A_37) | ~v4_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.03/1.50  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.50  tff(c_332, plain, (![A_155, B_156, C_157, D_158]: (k1_enumset1(A_155, B_156, C_157)=D_158 | k2_tarski(A_155, C_157)=D_158 | k2_tarski(B_156, C_157)=D_158 | k2_tarski(A_155, B_156)=D_158 | k1_tarski(C_157)=D_158 | k1_tarski(B_156)=D_158 | k1_tarski(A_155)=D_158 | k1_xboole_0=D_158 | ~r1_tarski(D_158, k1_enumset1(A_155, B_156, C_157)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.03/1.50  tff(c_354, plain, (![A_3, B_4, D_158]: (k1_enumset1(A_3, A_3, B_4)=D_158 | k2_tarski(A_3, B_4)=D_158 | k2_tarski(A_3, B_4)=D_158 | k2_tarski(A_3, A_3)=D_158 | k1_tarski(B_4)=D_158 | k1_tarski(A_3)=D_158 | k1_tarski(A_3)=D_158 | k1_xboole_0=D_158 | ~r1_tarski(D_158, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_332])).
% 3.03/1.50  tff(c_408, plain, (![A_169, B_170, D_171]: (k2_tarski(A_169, B_170)=D_171 | k2_tarski(A_169, B_170)=D_171 | k2_tarski(A_169, B_170)=D_171 | k1_tarski(A_169)=D_171 | k1_tarski(B_170)=D_171 | k1_tarski(A_169)=D_171 | k1_tarski(A_169)=D_171 | k1_xboole_0=D_171 | ~r1_tarski(D_171, k2_tarski(A_169, B_170)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_354])).
% 3.03/1.50  tff(c_447, plain, (![A_172, B_173, B_174]: (k2_tarski(A_172, B_173)=k1_relat_1(B_174) | k1_tarski(B_173)=k1_relat_1(B_174) | k1_tarski(A_172)=k1_relat_1(B_174) | k1_relat_1(B_174)=k1_xboole_0 | ~v4_relat_1(B_174, k2_tarski(A_172, B_173)) | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_40, c_408])).
% 3.03/1.50  tff(c_450, plain, (![A_2, B_174]: (k2_tarski(A_2, A_2)=k1_relat_1(B_174) | k1_tarski(A_2)=k1_relat_1(B_174) | k1_tarski(A_2)=k1_relat_1(B_174) | k1_relat_1(B_174)=k1_xboole_0 | ~v4_relat_1(B_174, k1_tarski(A_2)) | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_4, c_447])).
% 3.03/1.50  tff(c_452, plain, (![A_175, B_176]: (k1_tarski(A_175)=k1_relat_1(B_176) | k1_tarski(A_175)=k1_relat_1(B_176) | k1_tarski(A_175)=k1_relat_1(B_176) | k1_relat_1(B_176)=k1_xboole_0 | ~v4_relat_1(B_176, k1_tarski(A_175)) | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_450])).
% 3.03/1.50  tff(c_458, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_191, c_452])).
% 3.03/1.50  tff(c_461, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_158, c_458])).
% 3.03/1.50  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_290, c_461])).
% 3.03/1.50  tff(c_464, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_288])).
% 3.03/1.50  tff(c_534, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_464])).
% 3.03/1.50  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_534])).
% 3.03/1.50  tff(c_539, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_165])).
% 3.03/1.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.03/1.50  tff(c_544, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_2])).
% 3.03/1.50  tff(c_46, plain, (![A_43]: (k9_relat_1(k1_xboole_0, A_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.03/1.50  tff(c_543, plain, (![A_43]: (k9_relat_1('#skF_4', A_43)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_539, c_46])).
% 3.03/1.50  tff(c_713, plain, (![A_225, B_226, C_227, D_228]: (k7_relset_1(A_225, B_226, C_227, D_228)=k9_relat_1(C_227, D_228) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.03/1.50  tff(c_715, plain, (![D_228]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_228)=k9_relat_1('#skF_4', D_228))), inference(resolution, [status(thm)], [c_64, c_713])).
% 3.03/1.50  tff(c_717, plain, (![D_228]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_228)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_543, c_715])).
% 3.03/1.50  tff(c_718, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_60])).
% 3.03/1.50  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_544, c_718])).
% 3.03/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  
% 3.03/1.50  Inference rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Ref     : 0
% 3.03/1.50  #Sup     : 141
% 3.03/1.50  #Fact    : 0
% 3.03/1.50  #Define  : 0
% 3.03/1.50  #Split   : 4
% 3.03/1.50  #Chain   : 0
% 3.03/1.50  #Close   : 0
% 3.03/1.50  
% 3.03/1.50  Ordering : KBO
% 3.03/1.50  
% 3.03/1.50  Simplification rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Subsume      : 13
% 3.03/1.50  #Demod        : 82
% 3.03/1.50  #Tautology    : 82
% 3.03/1.50  #SimpNegUnit  : 1
% 3.03/1.50  #BackRed      : 11
% 3.03/1.50  
% 3.03/1.50  #Partial instantiations: 0
% 3.03/1.50  #Strategies tried      : 1
% 3.03/1.50  
% 3.03/1.50  Timing (in seconds)
% 3.03/1.50  ----------------------
% 3.03/1.51  Preprocessing        : 0.34
% 3.03/1.51  Parsing              : 0.18
% 3.03/1.51  CNF conversion       : 0.02
% 3.03/1.51  Main loop            : 0.36
% 3.03/1.51  Inferencing          : 0.13
% 3.03/1.51  Reduction            : 0.12
% 3.03/1.51  Demodulation         : 0.09
% 3.03/1.51  BG Simplification    : 0.02
% 3.03/1.51  Subsumption          : 0.05
% 3.03/1.51  Abstraction          : 0.02
% 3.03/1.51  MUC search           : 0.00
% 3.03/1.51  Cooper               : 0.00
% 3.03/1.51  Total                : 0.73
% 3.03/1.51  Index Insertion      : 0.00
% 3.03/1.51  Index Deletion       : 0.00
% 3.03/1.51  Index Matching       : 0.00
% 3.03/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
