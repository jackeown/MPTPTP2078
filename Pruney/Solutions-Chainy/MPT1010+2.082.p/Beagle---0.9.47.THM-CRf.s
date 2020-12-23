%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 102 expanded)
%              Number of leaves         :   42 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 178 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : ~ v1_xboole_0(k4_enumset1(A,B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_subset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_77,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_122,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_126,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_122])).

tff(c_210,plain,(
    ! [B_144,A_145,C_146] :
      ( k1_xboole_0 = B_144
      | k1_relset_1(A_145,B_144,C_146) = A_145
      | ~ v1_funct_2(C_146,A_145,B_144)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_213,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_216,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_126,c_213])).

tff(c_217,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_176,plain,(
    ! [A_129,C_130] :
      ( r2_hidden(k4_tarski(A_129,k1_funct_1(C_130,A_129)),C_130)
      | ~ r2_hidden(A_129,k1_relat_1(C_130))
      | ~ v1_funct_1(C_130)
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [C_42,A_39,B_40] :
      ( r2_hidden(C_42,A_39)
      | ~ r2_hidden(C_42,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_234,plain,(
    ! [A_150,C_151,A_152] :
      ( r2_hidden(k4_tarski(A_150,k1_funct_1(C_151,A_150)),A_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(A_152))
      | ~ r2_hidden(A_150,k1_relat_1(C_151))
      | ~ v1_funct_1(C_151)
      | ~ v1_relat_1(C_151) ) ),
    inference(resolution,[status(thm)],[c_176,c_26])).

tff(c_20,plain,(
    ! [D_32,B_30,A_29,C_31] :
      ( D_32 = B_30
      | ~ r2_hidden(k4_tarski(A_29,B_30),k2_zfmisc_1(C_31,k1_tarski(D_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_262,plain,(
    ! [C_157,A_158,D_159,C_160] :
      ( k1_funct_1(C_157,A_158) = D_159
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(C_160,k1_tarski(D_159))))
      | ~ r2_hidden(A_158,k1_relat_1(C_157))
      | ~ v1_funct_1(C_157)
      | ~ v1_relat_1(C_157) ) ),
    inference(resolution,[status(thm)],[c_234,c_20])).

tff(c_264,plain,(
    ! [A_158] :
      ( k1_funct_1('#skF_4',A_158) = '#skF_2'
      | ~ r2_hidden(A_158,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_262])).

tff(c_268,plain,(
    ! [A_161] :
      ( k1_funct_1('#skF_4',A_161) = '#skF_2'
      | ~ r2_hidden(A_161,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_58,c_217,c_264])).

tff(c_279,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_268])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_279])).

tff(c_286,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    ! [C_99,A_100,B_101,D_102,E_103] : k4_enumset1(A_100,A_100,B_101,C_99,D_102,E_103) = k3_enumset1(A_100,B_101,C_99,D_102,E_103) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : ~ v1_xboole_0(k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [E_104,D_108,A_107,C_106,B_105] : ~ v1_xboole_0(k3_enumset1(A_107,B_105,C_106,D_108,E_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_24])).

tff(c_156,plain,(
    ! [A_111,B_112,C_113,D_114] : ~ v1_xboole_0(k2_enumset1(A_111,B_112,C_113,D_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_159,plain,(
    ! [A_115,B_116,C_117] : ~ v1_xboole_0(k1_enumset1(A_115,B_116,C_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_156])).

tff(c_162,plain,(
    ! [A_118,B_119] : ~ v1_xboole_0(k2_tarski(A_118,B_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_159])).

tff(c_164,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_162])).

tff(c_301,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_164])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:11:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.30  
% 2.21/1.30  %Foreground sorts:
% 2.21/1.30  
% 2.21/1.30  
% 2.21/1.30  %Background operators:
% 2.21/1.30  
% 2.21/1.30  
% 2.21/1.30  %Foreground operators:
% 2.21/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.30  
% 2.21/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.21/1.32  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.21/1.32  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.32  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.32  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.21/1.32  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.21/1.32  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.21/1.32  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.21/1.32  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.32  tff(f_30, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.32  tff(f_32, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.21/1.32  tff(f_34, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.21/1.32  tff(f_36, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.21/1.32  tff(f_49, axiom, (![A, B, C, D, E, F]: ~v1_xboole_0(k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_subset_1)).
% 2.21/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.21/1.32  tff(c_50, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.32  tff(c_52, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.32  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.32  tff(c_77, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.32  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_77])).
% 2.21/1.32  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.32  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.32  tff(c_122, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.32  tff(c_126, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_122])).
% 2.21/1.32  tff(c_210, plain, (![B_144, A_145, C_146]: (k1_xboole_0=B_144 | k1_relset_1(A_145, B_144, C_146)=A_145 | ~v1_funct_2(C_146, A_145, B_144) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.32  tff(c_213, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_210])).
% 2.21/1.32  tff(c_216, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_126, c_213])).
% 2.21/1.32  tff(c_217, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_216])).
% 2.21/1.32  tff(c_176, plain, (![A_129, C_130]: (r2_hidden(k4_tarski(A_129, k1_funct_1(C_130, A_129)), C_130) | ~r2_hidden(A_129, k1_relat_1(C_130)) | ~v1_funct_1(C_130) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.21/1.32  tff(c_26, plain, (![C_42, A_39, B_40]: (r2_hidden(C_42, A_39) | ~r2_hidden(C_42, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.32  tff(c_234, plain, (![A_150, C_151, A_152]: (r2_hidden(k4_tarski(A_150, k1_funct_1(C_151, A_150)), A_152) | ~m1_subset_1(C_151, k1_zfmisc_1(A_152)) | ~r2_hidden(A_150, k1_relat_1(C_151)) | ~v1_funct_1(C_151) | ~v1_relat_1(C_151))), inference(resolution, [status(thm)], [c_176, c_26])).
% 2.21/1.32  tff(c_20, plain, (![D_32, B_30, A_29, C_31]: (D_32=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), k2_zfmisc_1(C_31, k1_tarski(D_32))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.32  tff(c_262, plain, (![C_157, A_158, D_159, C_160]: (k1_funct_1(C_157, A_158)=D_159 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(C_160, k1_tarski(D_159)))) | ~r2_hidden(A_158, k1_relat_1(C_157)) | ~v1_funct_1(C_157) | ~v1_relat_1(C_157))), inference(resolution, [status(thm)], [c_234, c_20])).
% 2.21/1.32  tff(c_264, plain, (![A_158]: (k1_funct_1('#skF_4', A_158)='#skF_2' | ~r2_hidden(A_158, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_262])).
% 2.21/1.32  tff(c_268, plain, (![A_161]: (k1_funct_1('#skF_4', A_161)='#skF_2' | ~r2_hidden(A_161, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_58, c_217, c_264])).
% 2.21/1.32  tff(c_279, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_52, c_268])).
% 2.21/1.32  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_279])).
% 2.21/1.32  tff(c_286, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_216])).
% 2.21/1.32  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.21/1.32  tff(c_6, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.21/1.32  tff(c_8, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.32  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.32  tff(c_141, plain, (![C_99, A_100, B_101, D_102, E_103]: (k4_enumset1(A_100, A_100, B_101, C_99, D_102, E_103)=k3_enumset1(A_100, B_101, C_99, D_102, E_103))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.32  tff(c_24, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (~v1_xboole_0(k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.32  tff(c_152, plain, (![E_104, D_108, A_107, C_106, B_105]: (~v1_xboole_0(k3_enumset1(A_107, B_105, C_106, D_108, E_104)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_24])).
% 2.21/1.32  tff(c_156, plain, (![A_111, B_112, C_113, D_114]: (~v1_xboole_0(k2_enumset1(A_111, B_112, C_113, D_114)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_152])).
% 2.21/1.32  tff(c_159, plain, (![A_115, B_116, C_117]: (~v1_xboole_0(k1_enumset1(A_115, B_116, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_156])).
% 2.21/1.32  tff(c_162, plain, (![A_118, B_119]: (~v1_xboole_0(k2_tarski(A_118, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_159])).
% 2.21/1.32  tff(c_164, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_162])).
% 2.21/1.32  tff(c_301, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_286, c_164])).
% 2.21/1.32  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_301])).
% 2.21/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  Inference rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Ref     : 0
% 2.21/1.32  #Sup     : 58
% 2.21/1.32  #Fact    : 0
% 2.21/1.32  #Define  : 0
% 2.21/1.32  #Split   : 1
% 2.21/1.32  #Chain   : 0
% 2.21/1.32  #Close   : 0
% 2.21/1.32  
% 2.21/1.32  Ordering : KBO
% 2.21/1.32  
% 2.21/1.32  Simplification rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Subsume      : 0
% 2.21/1.32  #Demod        : 17
% 2.21/1.32  #Tautology    : 28
% 2.21/1.32  #SimpNegUnit  : 1
% 2.21/1.32  #BackRed      : 4
% 2.21/1.32  
% 2.21/1.32  #Partial instantiations: 0
% 2.21/1.32  #Strategies tried      : 1
% 2.21/1.32  
% 2.21/1.32  Timing (in seconds)
% 2.21/1.32  ----------------------
% 2.21/1.32  Preprocessing        : 0.34
% 2.21/1.32  Parsing              : 0.18
% 2.21/1.32  CNF conversion       : 0.02
% 2.21/1.32  Main loop            : 0.22
% 2.21/1.32  Inferencing          : 0.08
% 2.21/1.32  Reduction            : 0.07
% 2.21/1.32  Demodulation         : 0.05
% 2.21/1.32  BG Simplification    : 0.02
% 2.21/1.33  Subsumption          : 0.04
% 2.21/1.33  Abstraction          : 0.02
% 2.21/1.33  MUC search           : 0.00
% 2.21/1.33  Cooper               : 0.00
% 2.21/1.33  Total                : 0.60
% 2.21/1.33  Index Insertion      : 0.00
% 2.21/1.33  Index Deletion       : 0.00
% 2.21/1.33  Index Matching       : 0.00
% 2.21/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
