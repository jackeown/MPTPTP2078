%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:27 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 202 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 462 expanded)
%              Number of equality atoms :   26 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_55,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [A_13] : m1_subset_1('#skF_4',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_16])).

tff(c_324,plain,(
    ! [A_80,B_81] :
      ( r1_tarski('#skF_2'(A_80,B_81),B_81)
      | v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_516,plain,(
    ! [A_91] :
      ( r1_tarski('#skF_2'(A_91,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_61,c_324])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_10])).

tff(c_521,plain,(
    ! [A_92] :
      ( '#skF_2'(A_92,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_516,c_84])).

tff(c_524,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_521,c_34])).

tff(c_527,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_524])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_401,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_2'(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [B_19,A_17] :
      ( v4_pre_topc(B_19,A_17)
      | ~ v1_xboole_0(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1511,plain,(
    ! [A_130,B_131] :
      ( v4_pre_topc('#skF_2'(A_130,B_131),A_130)
      | ~ v1_xboole_0('#skF_2'(A_130,B_131))
      | ~ v2_pre_topc(A_130)
      | v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_401,c_20])).

tff(c_1833,plain,(
    ! [A_138] :
      ( v4_pre_topc('#skF_2'(A_138,'#skF_4'),A_138)
      | ~ v1_xboole_0('#skF_2'(A_138,'#skF_4'))
      | ~ v2_pre_topc(A_138)
      | v2_tex_2('#skF_4',A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_61,c_1511])).

tff(c_1836,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_1833])).

tff(c_1838,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_38,c_527,c_1836])).

tff(c_1839,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1838])).

tff(c_156,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_53,B_54] : r1_tarski(k4_xboole_0(A_53,B_54),A_53) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [B_54] : k4_xboole_0('#skF_4',B_54) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_86,c_84])).

tff(c_193,plain,(
    ! [B_64] : k3_xboole_0('#skF_4',B_64) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_198,plain,(
    ! [B_64] : k3_xboole_0(B_64,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_2])).

tff(c_250,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_252,plain,(
    ! [A_13,B_67] : k9_subset_1(A_13,B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_250])).

tff(c_254,plain,(
    ! [A_13,B_67] : k9_subset_1(A_13,B_67,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_252])).

tff(c_622,plain,(
    ! [A_98,B_99,D_100] :
      ( k9_subset_1(u1_struct_0(A_98),B_99,D_100) != '#skF_2'(A_98,B_99)
      | ~ v4_pre_topc(D_100,A_98)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(A_98)))
      | v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_625,plain,(
    ! [A_98,B_67] :
      ( '#skF_2'(A_98,B_67) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_98)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_98)))
      | v2_tex_2(B_67,A_98)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_622])).

tff(c_2486,plain,(
    ! [A_155,B_156] :
      ( '#skF_2'(A_155,B_156) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_155)
      | v2_tex_2(B_156,A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_625])).

tff(c_2500,plain,(
    ! [A_157] :
      ( '#skF_2'(A_157,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_157)
      | v2_tex_2('#skF_4',A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_61,c_2486])).

tff(c_2503,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1839,c_2500])).

tff(c_2509,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_527,c_2503])).

tff(c_2511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.84  
% 4.45/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.84  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.45/1.84  
% 4.45/1.84  %Foreground sorts:
% 4.45/1.84  
% 4.45/1.84  
% 4.45/1.84  %Background operators:
% 4.45/1.84  
% 4.45/1.84  
% 4.45/1.84  %Foreground operators:
% 4.45/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.45/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.84  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.45/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.45/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.45/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.45/1.84  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.45/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.84  
% 4.45/1.85  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 4.45/1.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.45/1.85  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.45/1.85  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 4.45/1.85  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.45/1.85  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 4.45/1.85  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.45/1.85  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.45/1.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.45/1.85  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.45/1.85  tff(c_34, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.45/1.85  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.45/1.85  tff(c_38, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.45/1.85  tff(c_55, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/1.85  tff(c_59, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_55])).
% 4.45/1.85  tff(c_16, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.85  tff(c_61, plain, (![A_13]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_16])).
% 4.45/1.85  tff(c_324, plain, (![A_80, B_81]: (r1_tarski('#skF_2'(A_80, B_81), B_81) | v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.45/1.85  tff(c_516, plain, (![A_91]: (r1_tarski('#skF_2'(A_91, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_61, c_324])).
% 4.45/1.85  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.45/1.85  tff(c_84, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_10])).
% 4.45/1.85  tff(c_521, plain, (![A_92]: ('#skF_2'(A_92, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_516, c_84])).
% 4.45/1.85  tff(c_524, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_521, c_34])).
% 4.45/1.85  tff(c_527, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_524])).
% 4.45/1.85  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.45/1.85  tff(c_401, plain, (![A_85, B_86]: (m1_subset_1('#skF_2'(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.45/1.85  tff(c_20, plain, (![B_19, A_17]: (v4_pre_topc(B_19, A_17) | ~v1_xboole_0(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.45/1.85  tff(c_1511, plain, (![A_130, B_131]: (v4_pre_topc('#skF_2'(A_130, B_131), A_130) | ~v1_xboole_0('#skF_2'(A_130, B_131)) | ~v2_pre_topc(A_130) | v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_401, c_20])).
% 4.45/1.85  tff(c_1833, plain, (![A_138]: (v4_pre_topc('#skF_2'(A_138, '#skF_4'), A_138) | ~v1_xboole_0('#skF_2'(A_138, '#skF_4')) | ~v2_pre_topc(A_138) | v2_tex_2('#skF_4', A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_61, c_1511])).
% 4.45/1.85  tff(c_1836, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_527, c_1833])).
% 4.45/1.85  tff(c_1838, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_38, c_527, c_1836])).
% 4.45/1.85  tff(c_1839, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_1838])).
% 4.45/1.85  tff(c_156, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/1.85  tff(c_86, plain, (![A_53, B_54]: (r1_tarski(k4_xboole_0(A_53, B_54), A_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.45/1.85  tff(c_94, plain, (![B_54]: (k4_xboole_0('#skF_4', B_54)='#skF_4')), inference(resolution, [status(thm)], [c_86, c_84])).
% 4.45/1.85  tff(c_193, plain, (![B_64]: (k3_xboole_0('#skF_4', B_64)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_156, c_94])).
% 4.45/1.85  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.85  tff(c_198, plain, (![B_64]: (k3_xboole_0(B_64, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_193, c_2])).
% 4.45/1.85  tff(c_250, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.45/1.85  tff(c_252, plain, (![A_13, B_67]: (k9_subset_1(A_13, B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_61, c_250])).
% 4.45/1.85  tff(c_254, plain, (![A_13, B_67]: (k9_subset_1(A_13, B_67, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_252])).
% 4.45/1.85  tff(c_622, plain, (![A_98, B_99, D_100]: (k9_subset_1(u1_struct_0(A_98), B_99, D_100)!='#skF_2'(A_98, B_99) | ~v4_pre_topc(D_100, A_98) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(A_98))) | v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.45/1.85  tff(c_625, plain, (![A_98, B_67]: ('#skF_2'(A_98, B_67)!='#skF_4' | ~v4_pre_topc('#skF_4', A_98) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_98))) | v2_tex_2(B_67, A_98) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(superposition, [status(thm), theory('equality')], [c_254, c_622])).
% 4.45/1.85  tff(c_2486, plain, (![A_155, B_156]: ('#skF_2'(A_155, B_156)!='#skF_4' | ~v4_pre_topc('#skF_4', A_155) | v2_tex_2(B_156, A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_625])).
% 4.45/1.85  tff(c_2500, plain, (![A_157]: ('#skF_2'(A_157, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_157) | v2_tex_2('#skF_4', A_157) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_61, c_2486])).
% 4.45/1.85  tff(c_2503, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1839, c_2500])).
% 4.45/1.85  tff(c_2509, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_527, c_2503])).
% 4.45/1.85  tff(c_2511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2509])).
% 4.45/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.85  
% 4.45/1.85  Inference rules
% 4.45/1.85  ----------------------
% 4.45/1.85  #Ref     : 0
% 4.45/1.85  #Sup     : 592
% 4.45/1.85  #Fact    : 0
% 4.45/1.85  #Define  : 0
% 4.45/1.85  #Split   : 0
% 4.45/1.85  #Chain   : 0
% 4.45/1.85  #Close   : 0
% 4.45/1.85  
% 4.45/1.85  Ordering : KBO
% 4.45/1.85  
% 4.45/1.85  Simplification rules
% 4.45/1.85  ----------------------
% 4.45/1.85  #Subsume      : 10
% 4.45/1.85  #Demod        : 845
% 4.45/1.85  #Tautology    : 390
% 4.45/1.85  #SimpNegUnit  : 8
% 4.45/1.85  #BackRed      : 3
% 4.45/1.85  
% 4.45/1.85  #Partial instantiations: 0
% 4.45/1.85  #Strategies tried      : 1
% 4.45/1.85  
% 4.45/1.85  Timing (in seconds)
% 4.45/1.85  ----------------------
% 4.45/1.86  Preprocessing        : 0.33
% 4.45/1.86  Parsing              : 0.17
% 4.45/1.86  CNF conversion       : 0.02
% 4.45/1.86  Main loop            : 0.73
% 4.45/1.86  Inferencing          : 0.21
% 4.45/1.86  Reduction            : 0.38
% 4.45/1.86  Demodulation         : 0.33
% 4.45/1.86  BG Simplification    : 0.03
% 4.45/1.86  Subsumption          : 0.09
% 4.45/1.86  Abstraction          : 0.04
% 4.45/1.86  MUC search           : 0.00
% 4.45/1.86  Cooper               : 0.00
% 4.45/1.86  Total                : 1.10
% 4.45/1.86  Index Insertion      : 0.00
% 4.45/1.86  Index Deletion       : 0.00
% 4.45/1.86  Index Matching       : 0.00
% 4.45/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
