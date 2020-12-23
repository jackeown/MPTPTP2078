%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:02 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 132 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 213 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_58,B_57] : r1_tarski(A_58,k2_xboole_0(B_57,A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_2])).

tff(c_415,plain,(
    ! [C_107,A_108,B_109] :
      ( r1_tarski(k2_zfmisc_1(C_107,A_108),k2_zfmisc_1(C_107,B_109))
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_239,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_247,plain,(
    ! [A_18,B_74,A_75] :
      ( v5_relat_1(A_18,B_74)
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_75,B_74)) ) ),
    inference(resolution,[status(thm)],[c_20,c_239])).

tff(c_426,plain,(
    ! [C_107,A_108,B_109] :
      ( v5_relat_1(k2_zfmisc_1(C_107,A_108),B_109)
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_415,c_247])).

tff(c_38,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_539,plain,(
    ! [C_134,A_135,B_136] :
      ( v5_relat_1(C_134,A_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(B_136))
      | ~ v5_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_543,plain,(
    ! [A_135] :
      ( v5_relat_1('#skF_3',A_135)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_2'),A_135)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_539])).

tff(c_548,plain,(
    ! [A_137] :
      ( v5_relat_1('#skF_3',A_137)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_2'),A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_543])).

tff(c_571,plain,(
    ! [B_109] :
      ( v5_relat_1('#skF_3',B_109)
      | ~ r1_tarski('#skF_2',B_109) ) ),
    inference(resolution,[status(thm)],[c_426,c_548])).

tff(c_188,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_194,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_188])).

tff(c_198,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_194])).

tff(c_34,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v5_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_461,plain,(
    ! [A_119,C_120,B_121] :
      ( r1_tarski(k2_zfmisc_1(A_119,C_120),k2_zfmisc_1(B_121,C_120))
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_347,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_355,plain,(
    ! [A_18,A_94,B_95] :
      ( v4_relat_1(A_18,A_94)
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_94,B_95)) ) ),
    inference(resolution,[status(thm)],[c_20,c_347])).

tff(c_471,plain,(
    ! [A_119,C_120,B_121] :
      ( v4_relat_1(k2_zfmisc_1(A_119,C_120),B_121)
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(resolution,[status(thm)],[c_461,c_355])).

tff(c_611,plain,(
    ! [C_141,A_142,B_143] :
      ( v4_relat_1(C_141,A_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(B_143))
      | ~ v4_relat_1(B_143,A_142)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_615,plain,(
    ! [A_142] :
      ( v4_relat_1('#skF_3',A_142)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_1','#skF_2'),A_142)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_611])).

tff(c_620,plain,(
    ! [A_144] :
      ( v4_relat_1('#skF_3',A_144)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_1','#skF_2'),A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_615])).

tff(c_641,plain,(
    ! [B_121] :
      ( v4_relat_1('#skF_3',B_121)
      | ~ r1_tarski('#skF_1',B_121) ) ),
    inference(resolution,[status(thm)],[c_471,c_620])).

tff(c_30,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_relat_1(B_32),A_31)
      | ~ v4_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_35] :
      ( k2_xboole_0(k1_relat_1(A_35),k2_relat_1(A_35)) = k3_relat_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_506,plain,(
    ! [A_129,C_130,B_131] :
      ( r1_tarski(k2_xboole_0(A_129,C_130),B_131)
      | ~ r1_tarski(C_130,B_131)
      | ~ r1_tarski(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_981,plain,(
    ! [A_173,B_174] :
      ( r1_tarski(k3_relat_1(A_173),B_174)
      | ~ r1_tarski(k2_relat_1(A_173),B_174)
      | ~ r1_tarski(k1_relat_1(A_173),B_174)
      | ~ v1_relat_1(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_506])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_999,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_981,c_44])).

tff(c_1007,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_999])).

tff(c_1040,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1007])).

tff(c_1043,plain,
    ( ~ v4_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1040])).

tff(c_1046,plain,(
    ~ v4_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1043])).

tff(c_1052,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_641,c_1046])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1052])).

tff(c_1060,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1007])).

tff(c_1064,plain,
    ( ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1060])).

tff(c_1067,plain,(
    ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1064])).

tff(c_1073,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_571,c_1067])).

tff(c_1080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:47:23 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.51  
% 3.41/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.52  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.52  
% 3.41/1.52  %Foreground sorts:
% 3.41/1.52  
% 3.41/1.52  
% 3.41/1.52  %Background operators:
% 3.41/1.52  
% 3.41/1.52  
% 3.41/1.52  %Foreground operators:
% 3.41/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.52  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.41/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.41/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.41/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.41/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.41/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.52  
% 3.48/1.53  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.48/1.53  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.48/1.53  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.48/1.53  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.48/1.53  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.53  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.48/1.53  tff(f_94, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.48/1.53  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.48/1.53  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 3.48/1.53  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.48/1.53  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.48/1.53  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_relat_1)).
% 3.48/1.53  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.48/1.53  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.48/1.53  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.48/1.53  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.53  tff(c_82, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.53  tff(c_116, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_6, c_82])).
% 3.48/1.53  tff(c_12, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.53  tff(c_139, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_116, c_12])).
% 3.48/1.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.53  tff(c_154, plain, (![A_58, B_57]: (r1_tarski(A_58, k2_xboole_0(B_57, A_58)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_2])).
% 3.48/1.53  tff(c_415, plain, (![C_107, A_108, B_109]: (r1_tarski(k2_zfmisc_1(C_107, A_108), k2_zfmisc_1(C_107, B_109)) | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.53  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.53  tff(c_239, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.48/1.53  tff(c_247, plain, (![A_18, B_74, A_75]: (v5_relat_1(A_18, B_74) | ~r1_tarski(A_18, k2_zfmisc_1(A_75, B_74)))), inference(resolution, [status(thm)], [c_20, c_239])).
% 3.48/1.53  tff(c_426, plain, (![C_107, A_108, B_109]: (v5_relat_1(k2_zfmisc_1(C_107, A_108), B_109) | ~r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_415, c_247])).
% 3.48/1.53  tff(c_38, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.48/1.53  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.48/1.53  tff(c_539, plain, (![C_134, A_135, B_136]: (v5_relat_1(C_134, A_135) | ~m1_subset_1(C_134, k1_zfmisc_1(B_136)) | ~v5_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.53  tff(c_543, plain, (![A_135]: (v5_relat_1('#skF_3', A_135) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'), A_135) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_539])).
% 3.48/1.53  tff(c_548, plain, (![A_137]: (v5_relat_1('#skF_3', A_137) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'), A_137))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_543])).
% 3.48/1.53  tff(c_571, plain, (![B_109]: (v5_relat_1('#skF_3', B_109) | ~r1_tarski('#skF_2', B_109))), inference(resolution, [status(thm)], [c_426, c_548])).
% 3.48/1.53  tff(c_188, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.53  tff(c_194, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_188])).
% 3.48/1.53  tff(c_198, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_194])).
% 3.48/1.53  tff(c_34, plain, (![B_34, A_33]: (r1_tarski(k2_relat_1(B_34), A_33) | ~v5_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.48/1.53  tff(c_461, plain, (![A_119, C_120, B_121]: (r1_tarski(k2_zfmisc_1(A_119, C_120), k2_zfmisc_1(B_121, C_120)) | ~r1_tarski(A_119, B_121))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.53  tff(c_347, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.48/1.53  tff(c_355, plain, (![A_18, A_94, B_95]: (v4_relat_1(A_18, A_94) | ~r1_tarski(A_18, k2_zfmisc_1(A_94, B_95)))), inference(resolution, [status(thm)], [c_20, c_347])).
% 3.48/1.53  tff(c_471, plain, (![A_119, C_120, B_121]: (v4_relat_1(k2_zfmisc_1(A_119, C_120), B_121) | ~r1_tarski(A_119, B_121))), inference(resolution, [status(thm)], [c_461, c_355])).
% 3.48/1.53  tff(c_611, plain, (![C_141, A_142, B_143]: (v4_relat_1(C_141, A_142) | ~m1_subset_1(C_141, k1_zfmisc_1(B_143)) | ~v4_relat_1(B_143, A_142) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.53  tff(c_615, plain, (![A_142]: (v4_relat_1('#skF_3', A_142) | ~v4_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'), A_142) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_611])).
% 3.48/1.53  tff(c_620, plain, (![A_144]: (v4_relat_1('#skF_3', A_144) | ~v4_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'), A_144))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_615])).
% 3.48/1.53  tff(c_641, plain, (![B_121]: (v4_relat_1('#skF_3', B_121) | ~r1_tarski('#skF_1', B_121))), inference(resolution, [status(thm)], [c_471, c_620])).
% 3.48/1.53  tff(c_30, plain, (![B_32, A_31]: (r1_tarski(k1_relat_1(B_32), A_31) | ~v4_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.48/1.53  tff(c_36, plain, (![A_35]: (k2_xboole_0(k1_relat_1(A_35), k2_relat_1(A_35))=k3_relat_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.48/1.53  tff(c_506, plain, (![A_129, C_130, B_131]: (r1_tarski(k2_xboole_0(A_129, C_130), B_131) | ~r1_tarski(C_130, B_131) | ~r1_tarski(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.53  tff(c_981, plain, (![A_173, B_174]: (r1_tarski(k3_relat_1(A_173), B_174) | ~r1_tarski(k2_relat_1(A_173), B_174) | ~r1_tarski(k1_relat_1(A_173), B_174) | ~v1_relat_1(A_173))), inference(superposition, [status(thm), theory('equality')], [c_36, c_506])).
% 3.48/1.53  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.48/1.53  tff(c_999, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_981, c_44])).
% 3.48/1.53  tff(c_1007, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_999])).
% 3.48/1.53  tff(c_1040, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1007])).
% 3.48/1.53  tff(c_1043, plain, (~v4_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1040])).
% 3.48/1.53  tff(c_1046, plain, (~v4_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1043])).
% 3.48/1.53  tff(c_1052, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_641, c_1046])).
% 3.48/1.53  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1052])).
% 3.48/1.53  tff(c_1060, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1007])).
% 3.48/1.53  tff(c_1064, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1060])).
% 3.48/1.53  tff(c_1067, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1064])).
% 3.48/1.53  tff(c_1073, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_571, c_1067])).
% 3.48/1.53  tff(c_1080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_1073])).
% 3.48/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.53  
% 3.48/1.53  Inference rules
% 3.48/1.53  ----------------------
% 3.48/1.54  #Ref     : 0
% 3.48/1.54  #Sup     : 225
% 3.48/1.54  #Fact    : 0
% 3.48/1.54  #Define  : 0
% 3.48/1.54  #Split   : 4
% 3.48/1.54  #Chain   : 0
% 3.48/1.54  #Close   : 0
% 3.48/1.54  
% 3.48/1.54  Ordering : KBO
% 3.48/1.54  
% 3.48/1.54  Simplification rules
% 3.48/1.54  ----------------------
% 3.48/1.54  #Subsume      : 33
% 3.48/1.54  #Demod        : 87
% 3.48/1.54  #Tautology    : 68
% 3.48/1.54  #SimpNegUnit  : 0
% 3.48/1.54  #BackRed      : 0
% 3.48/1.54  
% 3.48/1.54  #Partial instantiations: 0
% 3.48/1.54  #Strategies tried      : 1
% 3.48/1.54  
% 3.48/1.54  Timing (in seconds)
% 3.48/1.54  ----------------------
% 3.48/1.54  Preprocessing        : 0.33
% 3.48/1.54  Parsing              : 0.18
% 3.48/1.54  CNF conversion       : 0.02
% 3.48/1.54  Main loop            : 0.45
% 3.48/1.54  Inferencing          : 0.16
% 3.48/1.54  Reduction            : 0.15
% 3.48/1.54  Demodulation         : 0.11
% 3.48/1.54  BG Simplification    : 0.02
% 3.48/1.54  Subsumption          : 0.08
% 3.48/1.54  Abstraction          : 0.02
% 3.48/1.54  MUC search           : 0.00
% 3.48/1.54  Cooper               : 0.00
% 3.48/1.54  Total                : 0.82
% 3.48/1.54  Index Insertion      : 0.00
% 3.48/1.54  Index Deletion       : 0.00
% 3.48/1.54  Index Matching       : 0.00
% 3.48/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
