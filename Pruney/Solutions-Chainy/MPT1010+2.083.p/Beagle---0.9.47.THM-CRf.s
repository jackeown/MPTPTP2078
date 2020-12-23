%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   77 (  87 expanded)
%              Number of leaves         :   44 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 133 expanded)
%              Number of equality atoms :   43 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_58,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_146,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_150,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_146])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_42] : k1_setfam_1(k1_tarski(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_101,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_104,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_101])).

tff(c_124,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_124])).

tff(c_136,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_26,plain,(
    ! [B_37] : k4_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) != k1_tarski(B_37) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [B_37] : k1_tarski(B_37) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_26])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_212,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_216,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_212])).

tff(c_292,plain,(
    ! [B_140,A_141,C_142] :
      ( k1_xboole_0 = B_140
      | k1_relset_1(A_141,B_140,C_142) = A_141
      | ~ v1_funct_2(C_142,A_141,B_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_295,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_292])).

tff(c_298,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_216,c_295])).

tff(c_299,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_298])).

tff(c_252,plain,(
    ! [A_124,C_125] :
      ( r2_hidden(k4_tarski(A_124,k1_funct_1(C_125,A_124)),C_125)
      | ~ r2_hidden(A_124,k1_relat_1(C_125))
      | ~ v1_funct_1(C_125)
      | ~ v1_relat_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [C_41,A_38,B_39] :
      ( r2_hidden(C_41,A_38)
      | ~ r2_hidden(C_41,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_309,plain,(
    ! [A_143,C_144,A_145] :
      ( r2_hidden(k4_tarski(A_143,k1_funct_1(C_144,A_143)),A_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_145))
      | ~ r2_hidden(A_143,k1_relat_1(C_144))
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_252,c_30])).

tff(c_22,plain,(
    ! [D_35,B_33,A_32,C_34] :
      ( D_35 = B_33
      | ~ r2_hidden(k4_tarski(A_32,B_33),k2_zfmisc_1(C_34,k1_tarski(D_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_337,plain,(
    ! [C_150,A_151,D_152,C_153] :
      ( k1_funct_1(C_150,A_151) = D_152
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(C_153,k1_tarski(D_152))))
      | ~ r2_hidden(A_151,k1_relat_1(C_150))
      | ~ v1_funct_1(C_150)
      | ~ v1_relat_1(C_150) ) ),
    inference(resolution,[status(thm)],[c_309,c_22])).

tff(c_339,plain,(
    ! [A_151] :
      ( k1_funct_1('#skF_4',A_151) = '#skF_2'
      | ~ r2_hidden(A_151,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_337])).

tff(c_354,plain,(
    ! [A_157] :
      ( k1_funct_1('#skF_4',A_157) = '#skF_2'
      | ~ r2_hidden(A_157,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_66,c_299,c_339])).

tff(c_365,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_60,c_354])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n005.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 16:37:47 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.40/1.32  
% 2.40/1.32  %Foreground sorts:
% 2.40/1.32  
% 2.40/1.32  
% 2.40/1.32  %Background operators:
% 2.40/1.32  
% 2.40/1.32  
% 2.40/1.32  %Foreground operators:
% 2.40/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.40/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.40/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.40/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.40/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.40/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.40/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.40/1.32  
% 2.63/1.33  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.63/1.33  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.63/1.33  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.63/1.33  tff(f_63, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.63/1.33  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.63/1.33  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.63/1.33  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.63/1.33  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.63/1.33  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.63/1.33  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.63/1.33  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.63/1.33  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.63/1.33  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.63/1.33  tff(c_58, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.63/1.33  tff(c_60, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.63/1.33  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.63/1.33  tff(c_146, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.63/1.33  tff(c_150, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_146])).
% 2.63/1.33  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.63/1.33  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.33  tff(c_32, plain, (![A_42]: (k1_setfam_1(k1_tarski(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.33  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.33  tff(c_92, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.33  tff(c_101, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_92])).
% 2.63/1.33  tff(c_104, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_101])).
% 2.63/1.33  tff(c_124, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.33  tff(c_133, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_104, c_124])).
% 2.63/1.33  tff(c_136, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_133])).
% 2.63/1.33  tff(c_26, plain, (![B_37]: (k4_xboole_0(k1_tarski(B_37), k1_tarski(B_37))!=k1_tarski(B_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.33  tff(c_137, plain, (![B_37]: (k1_tarski(B_37)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_26])).
% 2.63/1.33  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.63/1.33  tff(c_212, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.33  tff(c_216, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_212])).
% 2.63/1.33  tff(c_292, plain, (![B_140, A_141, C_142]: (k1_xboole_0=B_140 | k1_relset_1(A_141, B_140, C_142)=A_141 | ~v1_funct_2(C_142, A_141, B_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.33  tff(c_295, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_292])).
% 2.63/1.33  tff(c_298, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_216, c_295])).
% 2.63/1.33  tff(c_299, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_137, c_298])).
% 2.63/1.33  tff(c_252, plain, (![A_124, C_125]: (r2_hidden(k4_tarski(A_124, k1_funct_1(C_125, A_124)), C_125) | ~r2_hidden(A_124, k1_relat_1(C_125)) | ~v1_funct_1(C_125) | ~v1_relat_1(C_125))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.63/1.33  tff(c_30, plain, (![C_41, A_38, B_39]: (r2_hidden(C_41, A_38) | ~r2_hidden(C_41, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.33  tff(c_309, plain, (![A_143, C_144, A_145]: (r2_hidden(k4_tarski(A_143, k1_funct_1(C_144, A_143)), A_145) | ~m1_subset_1(C_144, k1_zfmisc_1(A_145)) | ~r2_hidden(A_143, k1_relat_1(C_144)) | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(resolution, [status(thm)], [c_252, c_30])).
% 2.63/1.33  tff(c_22, plain, (![D_35, B_33, A_32, C_34]: (D_35=B_33 | ~r2_hidden(k4_tarski(A_32, B_33), k2_zfmisc_1(C_34, k1_tarski(D_35))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.33  tff(c_337, plain, (![C_150, A_151, D_152, C_153]: (k1_funct_1(C_150, A_151)=D_152 | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(C_153, k1_tarski(D_152)))) | ~r2_hidden(A_151, k1_relat_1(C_150)) | ~v1_funct_1(C_150) | ~v1_relat_1(C_150))), inference(resolution, [status(thm)], [c_309, c_22])).
% 2.63/1.33  tff(c_339, plain, (![A_151]: (k1_funct_1('#skF_4', A_151)='#skF_2' | ~r2_hidden(A_151, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_337])).
% 2.63/1.33  tff(c_354, plain, (![A_157]: (k1_funct_1('#skF_4', A_157)='#skF_2' | ~r2_hidden(A_157, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_66, c_299, c_339])).
% 2.63/1.33  tff(c_365, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_60, c_354])).
% 2.63/1.33  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_365])).
% 2.63/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.33  
% 2.63/1.33  Inference rules
% 2.63/1.33  ----------------------
% 2.63/1.33  #Ref     : 0
% 2.63/1.33  #Sup     : 65
% 2.63/1.33  #Fact    : 0
% 2.63/1.33  #Define  : 0
% 2.63/1.33  #Split   : 0
% 2.63/1.33  #Chain   : 0
% 2.63/1.33  #Close   : 0
% 2.63/1.33  
% 2.63/1.33  Ordering : KBO
% 2.63/1.33  
% 2.63/1.33  Simplification rules
% 2.63/1.33  ----------------------
% 2.63/1.33  #Subsume      : 0
% 2.63/1.33  #Demod        : 14
% 2.63/1.33  #Tautology    : 42
% 2.63/1.33  #SimpNegUnit  : 5
% 2.63/1.33  #BackRed      : 2
% 2.63/1.33  
% 2.63/1.33  #Partial instantiations: 0
% 2.63/1.33  #Strategies tried      : 1
% 2.63/1.33  
% 2.63/1.33  Timing (in seconds)
% 2.63/1.33  ----------------------
% 2.63/1.33  Preprocessing        : 0.34
% 2.63/1.33  Parsing              : 0.18
% 2.63/1.33  CNF conversion       : 0.02
% 2.63/1.33  Main loop            : 0.23
% 2.63/1.33  Inferencing          : 0.09
% 2.63/1.33  Reduction            : 0.07
% 2.63/1.33  Demodulation         : 0.05
% 2.63/1.33  BG Simplification    : 0.02
% 2.63/1.33  Subsumption          : 0.04
% 2.63/1.33  Abstraction          : 0.02
% 2.63/1.33  MUC search           : 0.00
% 2.63/1.33  Cooper               : 0.00
% 2.63/1.33  Total                : 0.60
% 2.63/1.33  Index Insertion      : 0.00
% 2.63/1.33  Index Deletion       : 0.00
% 2.63/1.33  Index Matching       : 0.00
% 2.63/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
