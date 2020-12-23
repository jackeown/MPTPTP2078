%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:32 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 138 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 266 expanded)
%              Number of equality atoms :   35 (  57 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [A_20] :
      ( v3_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_5] : k4_xboole_0(A_5,'#skF_4') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_203,plain,(
    ! [A_81,B_82] :
      ( r1_tarski('#skF_2'(A_81,B_82),B_82)
      | v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_268,plain,(
    ! [A_86] :
      ( r1_tarski('#skF_2'(A_86,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_92,c_203])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k1_xboole_0
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = '#skF_4'
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_271,plain,(
    ! [A_86] :
      ( k4_xboole_0('#skF_2'(A_86,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_268,c_116])).

tff(c_274,plain,(
    ! [A_87] :
      ( '#skF_2'(A_87,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_271])).

tff(c_277,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_42])).

tff(c_280,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_277])).

tff(c_26,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_111,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_107])).

tff(c_8,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_4] : k3_xboole_0(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_8])).

tff(c_134,plain,(
    ! [A_69,B_70,C_71] :
      ( k9_subset_1(A_69,B_70,C_71) = k3_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,(
    ! [A_14,B_70] : k9_subset_1(A_14,B_70,'#skF_4') = k3_xboole_0(B_70,'#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_134])).

tff(c_141,plain,(
    ! [A_14,B_70] : k9_subset_1(A_14,B_70,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_138])).

tff(c_142,plain,(
    ! [A_72,C_73,B_74] :
      ( k9_subset_1(A_72,C_73,B_74) = k9_subset_1(A_72,B_74,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [A_14,B_74] : k9_subset_1(A_14,B_74,'#skF_4') = k9_subset_1(A_14,'#skF_4',B_74) ),
    inference(resolution,[status(thm)],[c_92,c_142])).

tff(c_232,plain,(
    ! [A_14,B_74] : k9_subset_1(A_14,'#skF_4',B_74) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_148])).

tff(c_464,plain,(
    ! [A_107,B_108,D_109] :
      ( k9_subset_1(u1_struct_0(A_107),B_108,D_109) != '#skF_2'(A_107,B_108)
      | ~ v3_pre_topc(D_109,A_107)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_467,plain,(
    ! [A_107,B_74] :
      ( '#skF_2'(A_107,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_74,A_107)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_107)))
      | v2_tex_2('#skF_4',A_107)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_464])).

tff(c_489,plain,(
    ! [A_110,B_111] :
      ( '#skF_2'(A_110,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | v2_tex_2('#skF_4',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_467])).

tff(c_495,plain,(
    ! [B_111] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_489])).

tff(c_506,plain,(
    ! [B_111] :
      ( ~ v3_pre_topc(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_280,c_495])).

tff(c_510,plain,(
    ! [B_112] :
      ( ~ v3_pre_topc(B_112,'#skF_3')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_506])).

tff(c_523,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_510])).

tff(c_527,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_523])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.59/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.59/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.59/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.59/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.59/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.40  
% 2.59/1.42  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.59/1.42  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.59/1.42  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.59/1.42  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.59/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.59/1.42  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.59/1.42  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.59/1.42  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.59/1.42  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.59/1.42  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.59/1.42  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.59/1.42  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.59/1.42  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.59/1.42  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.59/1.42  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.59/1.42  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.59/1.42  tff(c_28, plain, (![A_20]: (v3_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.42  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.42  tff(c_16, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.42  tff(c_53, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.59/1.42  tff(c_42, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.59/1.42  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.59/1.42  tff(c_64, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.42  tff(c_68, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_64])).
% 2.59/1.42  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.42  tff(c_74, plain, (![A_5]: (k4_xboole_0(A_5, '#skF_4')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10])).
% 2.59/1.42  tff(c_20, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.42  tff(c_92, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 2.59/1.42  tff(c_203, plain, (![A_81, B_82]: (r1_tarski('#skF_2'(A_81, B_82), B_82) | v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.59/1.42  tff(c_268, plain, (![A_86]: (r1_tarski('#skF_2'(A_86, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_92, c_203])).
% 2.59/1.42  tff(c_6, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k1_xboole_0 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.42  tff(c_116, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)='#skF_4' | ~r1_tarski(A_2, B_3))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6])).
% 2.59/1.42  tff(c_271, plain, (![A_86]: (k4_xboole_0('#skF_2'(A_86, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_268, c_116])).
% 2.59/1.42  tff(c_274, plain, (![A_87]: ('#skF_2'(A_87, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_87) | ~l1_pre_topc(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_271])).
% 2.59/1.42  tff(c_277, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_274, c_42])).
% 2.59/1.42  tff(c_280, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_277])).
% 2.59/1.42  tff(c_26, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.59/1.42  tff(c_102, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.42  tff(c_107, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_26, c_102])).
% 2.59/1.42  tff(c_111, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_107])).
% 2.59/1.42  tff(c_8, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.42  tff(c_84, plain, (![A_4]: (k3_xboole_0(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_8])).
% 2.59/1.42  tff(c_134, plain, (![A_69, B_70, C_71]: (k9_subset_1(A_69, B_70, C_71)=k3_xboole_0(B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.42  tff(c_138, plain, (![A_14, B_70]: (k9_subset_1(A_14, B_70, '#skF_4')=k3_xboole_0(B_70, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_134])).
% 2.59/1.42  tff(c_141, plain, (![A_14, B_70]: (k9_subset_1(A_14, B_70, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_138])).
% 2.59/1.42  tff(c_142, plain, (![A_72, C_73, B_74]: (k9_subset_1(A_72, C_73, B_74)=k9_subset_1(A_72, B_74, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.42  tff(c_148, plain, (![A_14, B_74]: (k9_subset_1(A_14, B_74, '#skF_4')=k9_subset_1(A_14, '#skF_4', B_74))), inference(resolution, [status(thm)], [c_92, c_142])).
% 2.59/1.42  tff(c_232, plain, (![A_14, B_74]: (k9_subset_1(A_14, '#skF_4', B_74)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_148])).
% 2.59/1.42  tff(c_464, plain, (![A_107, B_108, D_109]: (k9_subset_1(u1_struct_0(A_107), B_108, D_109)!='#skF_2'(A_107, B_108) | ~v3_pre_topc(D_109, A_107) | ~m1_subset_1(D_109, k1_zfmisc_1(u1_struct_0(A_107))) | v2_tex_2(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.59/1.42  tff(c_467, plain, (![A_107, B_74]: ('#skF_2'(A_107, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_74, A_107) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_107))) | v2_tex_2('#skF_4', A_107) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_232, c_464])).
% 2.59/1.42  tff(c_489, plain, (![A_110, B_111]: ('#skF_2'(A_110, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | v2_tex_2('#skF_4', A_110) | ~l1_pre_topc(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_467])).
% 2.59/1.42  tff(c_495, plain, (![B_111]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v3_pre_topc(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_489])).
% 2.59/1.42  tff(c_506, plain, (![B_111]: (~v3_pre_topc(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_280, c_495])).
% 2.59/1.42  tff(c_510, plain, (![B_112]: (~v3_pre_topc(B_112, '#skF_3') | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_506])).
% 2.59/1.42  tff(c_523, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_53, c_510])).
% 2.59/1.42  tff(c_527, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_523])).
% 2.59/1.42  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_527])).
% 2.59/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.42  
% 2.59/1.42  Inference rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Ref     : 0
% 2.59/1.42  #Sup     : 102
% 2.59/1.42  #Fact    : 0
% 2.59/1.42  #Define  : 0
% 2.59/1.42  #Split   : 2
% 2.59/1.42  #Chain   : 0
% 2.59/1.42  #Close   : 0
% 2.59/1.42  
% 2.59/1.42  Ordering : KBO
% 2.59/1.42  
% 2.59/1.42  Simplification rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Subsume      : 4
% 2.59/1.42  #Demod        : 74
% 2.59/1.42  #Tautology    : 48
% 2.59/1.42  #SimpNegUnit  : 7
% 2.59/1.42  #BackRed      : 1
% 2.59/1.42  
% 2.59/1.42  #Partial instantiations: 0
% 2.59/1.42  #Strategies tried      : 1
% 2.59/1.42  
% 2.59/1.42  Timing (in seconds)
% 2.59/1.42  ----------------------
% 2.59/1.42  Preprocessing        : 0.31
% 2.59/1.42  Parsing              : 0.16
% 2.59/1.42  CNF conversion       : 0.02
% 2.59/1.42  Main loop            : 0.28
% 2.59/1.42  Inferencing          : 0.10
% 2.59/1.42  Reduction            : 0.09
% 2.59/1.42  Demodulation         : 0.06
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.05
% 2.59/1.42  Abstraction          : 0.02
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.63
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
