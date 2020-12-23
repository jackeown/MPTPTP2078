%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:31 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 148 expanded)
%              Number of leaves         :   38 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 289 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_21] :
      ( v3_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_194,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_235,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_24,c_194])).

tff(c_239,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_235])).

tff(c_358,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),B_89)
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_360,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_2'('#skF_3',B_89),B_89)
      | v2_tex_2(B_89,'#skF_3')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_358])).

tff(c_371,plain,(
    ! [B_90] :
      ( r1_tarski('#skF_2'('#skF_3',B_90),B_90)
      | v2_tex_2(B_90,'#skF_3')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_360])).

tff(c_377,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_371])).

tff(c_381,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_377])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_8])).

tff(c_385,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_381,c_82])).

tff(c_84,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    ! [B_59] : k3_xboole_0('#skF_4',B_59) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [B_59] : k3_xboole_0(B_59,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_253,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_257,plain,(
    ! [A_15,B_75] : k9_subset_1(A_15,B_75,'#skF_4') = k3_xboole_0(B_75,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_253])).

tff(c_260,plain,(
    ! [A_15,B_75] : k9_subset_1(A_15,B_75,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_257])).

tff(c_287,plain,(
    ! [A_81,C_82,B_83] :
      ( k9_subset_1(A_81,C_82,B_83) = k9_subset_1(A_81,B_83,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_291,plain,(
    ! [A_15,B_83] : k9_subset_1(A_15,B_83,'#skF_4') = k9_subset_1(A_15,'#skF_4',B_83) ),
    inference(resolution,[status(thm)],[c_72,c_287])).

tff(c_295,plain,(
    ! [A_15,B_83] : k9_subset_1(A_15,'#skF_4',B_83) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_291])).

tff(c_674,plain,(
    ! [A_125,B_126,D_127] :
      ( k9_subset_1(u1_struct_0(A_125),B_126,D_127) != '#skF_2'(A_125,B_126)
      | ~ v3_pre_topc(D_127,A_125)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(u1_struct_0(A_125)))
      | v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_684,plain,(
    ! [A_125,B_83] :
      ( '#skF_2'(A_125,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_83,A_125)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_125)))
      | v2_tex_2('#skF_4',A_125)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_674])).

tff(c_703,plain,(
    ! [A_128,B_129] :
      ( '#skF_2'(A_128,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | v2_tex_2('#skF_4',A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_684])).

tff(c_709,plain,(
    ! [B_129] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_703])).

tff(c_720,plain,(
    ! [B_129] :
      ( ~ v3_pre_topc(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_385,c_709])).

tff(c_724,plain,(
    ! [B_130] :
      ( ~ v3_pre_topc(B_130,'#skF_3')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_720])).

tff(c_737,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_724])).

tff(c_741,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_737])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.39  
% 2.96/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.39  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.96/1.39  
% 2.96/1.39  %Foreground sorts:
% 2.96/1.39  
% 2.96/1.39  
% 2.96/1.39  %Background operators:
% 2.96/1.39  
% 2.96/1.39  
% 2.96/1.39  %Foreground operators:
% 2.96/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.96/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.96/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.96/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.96/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.96/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.96/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.96/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.96/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.96/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.96/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.96/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.39  
% 2.96/1.40  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.96/1.40  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.96/1.40  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.96/1.40  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.96/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.96/1.40  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.96/1.40  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.96/1.40  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.96/1.40  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.96/1.40  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.96/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.96/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.40  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.96/1.40  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.96/1.40  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.96/1.40  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.96/1.40  tff(c_26, plain, (![A_21]: (v3_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.96/1.40  tff(c_12, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.40  tff(c_14, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.40  tff(c_51, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.96/1.40  tff(c_40, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.96/1.40  tff(c_44, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.96/1.40  tff(c_62, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.40  tff(c_66, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_62])).
% 2.96/1.40  tff(c_18, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.40  tff(c_72, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18])).
% 2.96/1.40  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.40  tff(c_194, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.40  tff(c_235, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_24, c_194])).
% 2.96/1.40  tff(c_239, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_235])).
% 2.96/1.40  tff(c_358, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), B_89) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.40  tff(c_360, plain, (![B_89]: (r1_tarski('#skF_2'('#skF_3', B_89), B_89) | v2_tex_2(B_89, '#skF_3') | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_358])).
% 2.96/1.40  tff(c_371, plain, (![B_90]: (r1_tarski('#skF_2'('#skF_3', B_90), B_90) | v2_tex_2(B_90, '#skF_3') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_360])).
% 2.96/1.40  tff(c_377, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_371])).
% 2.96/1.40  tff(c_381, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_377])).
% 2.96/1.40  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.40  tff(c_82, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_8])).
% 2.96/1.40  tff(c_385, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_381, c_82])).
% 2.96/1.40  tff(c_84, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.40  tff(c_129, plain, (![B_59]: (k3_xboole_0('#skF_4', B_59)='#skF_4')), inference(resolution, [status(thm)], [c_84, c_82])).
% 2.96/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.40  tff(c_134, plain, (![B_59]: (k3_xboole_0(B_59, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 2.96/1.40  tff(c_253, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.40  tff(c_257, plain, (![A_15, B_75]: (k9_subset_1(A_15, B_75, '#skF_4')=k3_xboole_0(B_75, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_253])).
% 2.96/1.40  tff(c_260, plain, (![A_15, B_75]: (k9_subset_1(A_15, B_75, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_257])).
% 2.96/1.40  tff(c_287, plain, (![A_81, C_82, B_83]: (k9_subset_1(A_81, C_82, B_83)=k9_subset_1(A_81, B_83, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.40  tff(c_291, plain, (![A_15, B_83]: (k9_subset_1(A_15, B_83, '#skF_4')=k9_subset_1(A_15, '#skF_4', B_83))), inference(resolution, [status(thm)], [c_72, c_287])).
% 2.96/1.40  tff(c_295, plain, (![A_15, B_83]: (k9_subset_1(A_15, '#skF_4', B_83)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_291])).
% 2.96/1.40  tff(c_674, plain, (![A_125, B_126, D_127]: (k9_subset_1(u1_struct_0(A_125), B_126, D_127)!='#skF_2'(A_125, B_126) | ~v3_pre_topc(D_127, A_125) | ~m1_subset_1(D_127, k1_zfmisc_1(u1_struct_0(A_125))) | v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.40  tff(c_684, plain, (![A_125, B_83]: ('#skF_2'(A_125, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_83, A_125) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_125))) | v2_tex_2('#skF_4', A_125) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(superposition, [status(thm), theory('equality')], [c_295, c_674])).
% 2.96/1.40  tff(c_703, plain, (![A_128, B_129]: ('#skF_2'(A_128, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | v2_tex_2('#skF_4', A_128) | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_684])).
% 2.96/1.40  tff(c_709, plain, (![B_129]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v3_pre_topc(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_703])).
% 2.96/1.40  tff(c_720, plain, (![B_129]: (~v3_pre_topc(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_385, c_709])).
% 2.96/1.40  tff(c_724, plain, (![B_130]: (~v3_pre_topc(B_130, '#skF_3') | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_720])).
% 2.96/1.40  tff(c_737, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_51, c_724])).
% 2.96/1.40  tff(c_741, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_737])).
% 2.96/1.40  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_741])).
% 2.96/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.40  
% 2.96/1.40  Inference rules
% 2.96/1.40  ----------------------
% 2.96/1.40  #Ref     : 0
% 2.96/1.40  #Sup     : 151
% 2.96/1.40  #Fact    : 0
% 2.96/1.40  #Define  : 0
% 2.96/1.40  #Split   : 1
% 2.96/1.40  #Chain   : 0
% 2.96/1.40  #Close   : 0
% 2.96/1.40  
% 2.96/1.40  Ordering : KBO
% 2.96/1.40  
% 2.96/1.40  Simplification rules
% 2.96/1.40  ----------------------
% 2.96/1.40  #Subsume      : 9
% 2.96/1.40  #Demod        : 118
% 2.96/1.40  #Tautology    : 84
% 2.96/1.41  #SimpNegUnit  : 11
% 2.96/1.41  #BackRed      : 2
% 2.96/1.41  
% 2.96/1.41  #Partial instantiations: 0
% 2.96/1.41  #Strategies tried      : 1
% 2.96/1.41  
% 2.96/1.41  Timing (in seconds)
% 2.96/1.41  ----------------------
% 2.96/1.41  Preprocessing        : 0.32
% 2.96/1.41  Parsing              : 0.17
% 2.96/1.41  CNF conversion       : 0.02
% 2.96/1.41  Main loop            : 0.33
% 2.96/1.41  Inferencing          : 0.12
% 2.96/1.41  Reduction            : 0.12
% 2.96/1.41  Demodulation         : 0.09
% 2.96/1.41  BG Simplification    : 0.02
% 2.96/1.41  Subsumption          : 0.05
% 2.96/1.41  Abstraction          : 0.02
% 2.96/1.41  MUC search           : 0.00
% 2.96/1.41  Cooper               : 0.00
% 2.96/1.41  Total                : 0.69
% 2.96/1.41  Index Insertion      : 0.00
% 2.96/1.41  Index Deletion       : 0.00
% 2.96/1.41  Index Matching       : 0.00
% 2.96/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
