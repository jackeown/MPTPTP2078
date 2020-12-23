%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:01 EST 2020

% Result     : Theorem 33.76s
% Output     : CNFRefutation 34.01s
% Verified   : 
% Statistics : Number of formulae       :  202 (1007 expanded)
%              Number of leaves         :   58 ( 364 expanded)
%              Depth                    :   19
%              Number of atoms          :  276 (1536 expanded)
%              Number of equality atoms :  112 ( 725 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_77,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_103,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_162,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_95,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_89,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_110,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),'#skF_7') != k2_tops_1('#skF_6','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_165,plain,(
    ~ v3_pre_topc('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_66,plain,(
    ! [B_35,A_34] : k2_tarski(B_35,A_34) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_319,plain,(
    ! [A_104,B_105] : k1_setfam_1(k2_tarski(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_339,plain,(
    ! [A_108,B_109] : k1_setfam_1(k2_tarski(A_108,B_109)) = k3_xboole_0(B_109,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_319])).

tff(c_84,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_362,plain,(
    ! [B_110,A_111] : k3_xboole_0(B_110,A_111) = k3_xboole_0(A_111,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_84])).

tff(c_166,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k2_xboole_0(A_87,B_88)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_171,plain,(
    ! [A_87] : r1_tarski(k1_xboole_0,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_56])).

tff(c_240,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_250,plain,(
    ! [A_87] : k3_xboole_0(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_240])).

tff(c_378,plain,(
    ! [B_110] : k3_xboole_0(B_110,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_250])).

tff(c_58,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_547,plain,(
    ! [A_125,B_126] : k2_xboole_0(k3_xboole_0(A_125,B_126),k4_xboole_0(A_125,B_126)) = A_125 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_577,plain,(
    ! [A_28] : k2_xboole_0(k3_xboole_0(A_28,k1_xboole_0),A_28) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_547])).

tff(c_599,plain,(
    ! [A_127] : k2_xboole_0(k1_xboole_0,A_127) = A_127 ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_577])).

tff(c_276,plain,(
    ! [A_100,B_101] : k3_tarski(k2_tarski(A_100,B_101)) = k2_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_485,plain,(
    ! [B_121,A_122] : k3_tarski(k2_tarski(B_121,A_122)) = k2_xboole_0(A_122,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_276])).

tff(c_68,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_491,plain,(
    ! [B_121,A_122] : k2_xboole_0(B_121,A_122) = k2_xboole_0(A_122,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_68])).

tff(c_605,plain,(
    ! [A_127] : k2_xboole_0(A_127,k1_xboole_0) = A_127 ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_491])).

tff(c_106,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_104,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2463,plain,(
    ! [A_205,B_206,C_207] :
      ( k7_subset_1(A_205,B_206,C_207) = k4_xboole_0(B_206,C_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(A_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2487,plain,(
    ! [C_207] : k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',C_207) = k4_xboole_0('#skF_7',C_207) ),
    inference(resolution,[status(thm)],[c_104,c_2463])).

tff(c_7606,plain,(
    ! [A_342,B_343] :
      ( k7_subset_1(u1_struct_0(A_342),B_343,k2_tops_1(A_342,B_343)) = k1_tops_1(A_342,B_343)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_7642,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_7606])).

tff(c_7663,plain,(
    k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2487,c_7642])).

tff(c_4191,plain,(
    ! [A_245,B_246] :
      ( m1_subset_1(k2_pre_topc(A_245,B_246),k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_80,plain,(
    ! [A_48,B_49,C_50] :
      ( k7_subset_1(A_48,B_49,C_50) = k4_xboole_0(B_49,C_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_25287,plain,(
    ! [A_618,B_619,C_620] :
      ( k7_subset_1(u1_struct_0(A_618),k2_pre_topc(A_618,B_619),C_620) = k4_xboole_0(k2_pre_topc(A_618,B_619),C_620)
      | ~ m1_subset_1(B_619,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ l1_pre_topc(A_618) ) ),
    inference(resolution,[status(thm)],[c_4191,c_80])).

tff(c_25338,plain,(
    ! [C_620] :
      ( k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),C_620) = k4_xboole_0(k2_pre_topc('#skF_6','#skF_7'),C_620)
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_104,c_25287])).

tff(c_25382,plain,(
    ! [C_621] : k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),C_621) = k4_xboole_0(k2_pre_topc('#skF_6','#skF_7'),C_621) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_25338])).

tff(c_116,plain,
    ( v3_pre_topc('#skF_7','#skF_6')
    | k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),'#skF_7') = k2_tops_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_271,plain,(
    k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),'#skF_7') = k2_tops_1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_116])).

tff(c_25396,plain,(
    k4_xboole_0(k2_pre_topc('#skF_6','#skF_7'),'#skF_7') = k2_tops_1('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_25382,c_271])).

tff(c_345,plain,(
    ! [B_109,A_108] : k3_xboole_0(B_109,A_108) = k3_xboole_0(A_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_84])).

tff(c_628,plain,(
    ! [A_128] : k2_xboole_0(A_128,k1_xboole_0) = A_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_491])).

tff(c_60,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_644,plain,(
    ! [A_128] : k4_xboole_0(A_128,A_128) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_60])).

tff(c_44,plain,(
    ! [A_18] : k3_xboole_0(A_18,A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1018,plain,(
    ! [A_143,B_144] : k5_xboole_0(A_143,k3_xboole_0(A_143,B_144)) = k4_xboole_0(A_143,B_144) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1042,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k4_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1018])).

tff(c_1048,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_1042])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2594,plain,(
    ! [D_213,A_214,B_215] :
      ( r2_hidden(D_213,k4_xboole_0(A_214,B_215))
      | r2_hidden(D_213,B_215)
      | ~ r2_hidden(D_213,A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27429,plain,(
    ! [A_641,A_642,B_643] :
      ( r1_tarski(A_641,k4_xboole_0(A_642,B_643))
      | r2_hidden('#skF_1'(A_641,k4_xboole_0(A_642,B_643)),B_643)
      | ~ r2_hidden('#skF_1'(A_641,k4_xboole_0(A_642,B_643)),A_642) ) ),
    inference(resolution,[status(thm)],[c_2594,c_4])).

tff(c_94901,plain,(
    ! [A_1233,B_1234] :
      ( r2_hidden('#skF_1'(A_1233,k4_xboole_0(A_1233,B_1234)),B_1234)
      | r1_tarski(A_1233,k4_xboole_0(A_1233,B_1234)) ) ),
    inference(resolution,[status(thm)],[c_6,c_27429])).

tff(c_1139,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_1'(A_156,B_157),A_156)
      | r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1169,plain,(
    ! [A_12,B_13,B_157] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_12,B_13),B_157),B_13)
      | r1_tarski(k4_xboole_0(A_12,B_13),B_157) ) ),
    inference(resolution,[status(thm)],[c_1139,c_28])).

tff(c_95392,plain,(
    ! [A_1235,B_1236] : r1_tarski(k4_xboole_0(A_1235,B_1236),k4_xboole_0(k4_xboole_0(A_1235,B_1236),B_1236)) ),
    inference(resolution,[status(thm)],[c_94901,c_1169])).

tff(c_668,plain,(
    ! [B_129,A_130] :
      ( B_129 = A_130
      | ~ r1_tarski(B_129,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_679,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,k4_xboole_0(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_56,c_668])).

tff(c_95878,plain,(
    ! [A_1237,B_1238] : k4_xboole_0(k4_xboole_0(A_1237,B_1238),B_1238) = k4_xboole_0(A_1237,B_1238) ),
    inference(resolution,[status(thm)],[c_95392,c_679])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11624,plain,(
    ! [A_423,B_424,B_425] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_423,B_424),B_425),A_423)
      | r1_tarski(k3_xboole_0(A_423,B_424),B_425) ) ),
    inference(resolution,[status(thm)],[c_1139,c_12])).

tff(c_11831,plain,(
    ! [A_423,B_424] : r1_tarski(k3_xboole_0(A_423,B_424),A_423) ),
    inference(resolution,[status(thm)],[c_11624,c_4])).

tff(c_52,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_588,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_577])).

tff(c_747,plain,(
    ! [A_133,B_134] : k4_xboole_0(k3_xboole_0(A_133,B_134),A_133) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_60])).

tff(c_64,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_752,plain,(
    ! [A_133,B_134] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_133,B_134),A_133),k1_xboole_0) = k3_xboole_0(A_133,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_64])).

tff(c_1854,plain,(
    ! [A_191,B_192] : k3_xboole_0(A_191,k3_xboole_0(A_191,B_192)) = k3_xboole_0(A_191,B_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_491,c_345,c_752])).

tff(c_1872,plain,(
    ! [A_191,B_192] : k5_xboole_0(A_191,k3_xboole_0(A_191,B_192)) = k4_xboole_0(A_191,k3_xboole_0(A_191,B_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_52])).

tff(c_1933,plain,(
    ! [A_191,B_192] : k4_xboole_0(A_191,k3_xboole_0(A_191,B_192)) = k4_xboole_0(A_191,B_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1872])).

tff(c_11859,plain,(
    ! [A_426,B_427] : r1_tarski(k3_xboole_0(A_426,B_427),A_426) ),
    inference(resolution,[status(thm)],[c_11624,c_4])).

tff(c_88,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,k1_zfmisc_1(B_55))
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1962,plain,(
    ! [A_195,B_196] :
      ( k4_xboole_0(A_195,B_196) = k3_subset_1(A_195,B_196)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1983,plain,(
    ! [B_55,A_54] :
      ( k4_xboole_0(B_55,A_54) = k3_subset_1(B_55,A_54)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_88,c_1962])).

tff(c_11871,plain,(
    ! [A_426,B_427] : k4_xboole_0(A_426,k3_xboole_0(A_426,B_427)) = k3_subset_1(A_426,k3_xboole_0(A_426,B_427)) ),
    inference(resolution,[status(thm)],[c_11859,c_1983])).

tff(c_13010,plain,(
    ! [A_445,B_446] : k3_subset_1(A_445,k3_xboole_0(A_445,B_446)) = k4_xboole_0(A_445,B_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1933,c_11871])).

tff(c_1787,plain,(
    ! [A_187,B_188] :
      ( k3_subset_1(A_187,k3_subset_1(A_187,B_188)) = B_188
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1798,plain,(
    ! [B_55,A_54] :
      ( k3_subset_1(B_55,k3_subset_1(B_55,A_54)) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_88,c_1787])).

tff(c_13020,plain,(
    ! [A_445,B_446] :
      ( k3_subset_1(A_445,k4_xboole_0(A_445,B_446)) = k3_xboole_0(A_445,B_446)
      | ~ r1_tarski(k3_xboole_0(A_445,B_446),A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13010,c_1798])).

tff(c_13115,plain,(
    ! [A_445,B_446] : k3_subset_1(A_445,k4_xboole_0(A_445,B_446)) = k3_xboole_0(A_445,B_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11831,c_13020])).

tff(c_78,plain,(
    ! [A_46,B_47] : k6_subset_1(A_46,B_47) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_74,plain,(
    ! [A_42,B_43] : m1_subset_1(k6_subset_1(A_42,B_43),k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_117,plain,(
    ! [A_42,B_43] : m1_subset_1(k4_xboole_0(A_42,B_43),k1_zfmisc_1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74])).

tff(c_1986,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_subset_1(A_42,k4_xboole_0(A_42,B_43)) ),
    inference(resolution,[status(thm)],[c_117,c_1962])).

tff(c_251,plain,(
    ! [A_26,B_27] : k3_xboole_0(k4_xboole_0(A_26,B_27),A_26) = k4_xboole_0(A_26,B_27) ),
    inference(resolution,[status(thm)],[c_56,c_240])).

tff(c_1479,plain,(
    ! [A_170,B_171] : k5_xboole_0(A_170,k3_xboole_0(B_171,A_170)) = k4_xboole_0(A_170,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1018])).

tff(c_1492,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_1479])).

tff(c_9420,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_subset_1(A_26,k4_xboole_0(A_26,B_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_1492])).

tff(c_13285,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13115,c_9420])).

tff(c_96058,plain,(
    ! [A_1237,B_1238] : k5_xboole_0(k4_xboole_0(A_1237,B_1238),k4_xboole_0(A_1237,B_1238)) = k3_xboole_0(k4_xboole_0(A_1237,B_1238),B_1238) ),
    inference(superposition,[status(thm),theory(equality)],[c_95878,c_13285])).

tff(c_96434,plain,(
    ! [B_1239,A_1240] : k3_xboole_0(B_1239,k4_xboole_0(A_1240,B_1239)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_1048,c_96058])).

tff(c_96934,plain,(
    k3_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25396,c_96434])).

tff(c_1381,plain,(
    ! [A_167,B_168] : k3_xboole_0(k4_xboole_0(A_167,B_168),A_167) = k4_xboole_0(A_167,B_168) ),
    inference(resolution,[status(thm)],[c_56,c_240])).

tff(c_1445,plain,(
    ! [A_108,B_168] : k3_xboole_0(A_108,k4_xboole_0(A_108,B_168)) = k4_xboole_0(A_108,B_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1381])).

tff(c_5869,plain,(
    ! [A_300,B_301] : k4_xboole_0(A_300,k4_xboole_0(A_300,B_301)) = k3_subset_1(A_300,k4_xboole_0(A_300,B_301)) ),
    inference(resolution,[status(thm)],[c_117,c_1962])).

tff(c_5905,plain,(
    ! [A_300,B_301] : k2_xboole_0(k3_xboole_0(A_300,k4_xboole_0(A_300,B_301)),k3_subset_1(A_300,k4_xboole_0(A_300,B_301))) = A_300 ),
    inference(superposition,[status(thm),theory(equality)],[c_5869,c_64])).

tff(c_5981,plain,(
    ! [A_300,B_301] : k2_xboole_0(k4_xboole_0(A_300,B_301),k3_subset_1(A_300,k4_xboole_0(A_300,B_301))) = A_300 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_5905])).

tff(c_13286,plain,(
    ! [A_300,B_301] : k2_xboole_0(k4_xboole_0(A_300,B_301),k3_xboole_0(A_300,B_301)) = A_300 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13115,c_5981])).

tff(c_97445,plain,(
    k2_xboole_0(k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')),k1_xboole_0) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_96934,c_13286])).

tff(c_97634,plain,(
    k1_tops_1('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_7663,c_97445])).

tff(c_108,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_30,plain,(
    ! [D_17,A_12,B_13] :
      ( r2_hidden(D_17,A_12)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10914,plain,(
    ! [A_404,B_405,B_406] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_404,B_405),B_406),A_404)
      | r1_tarski(k4_xboole_0(A_404,B_405),B_406) ) ),
    inference(resolution,[status(thm)],[c_1139,c_30])).

tff(c_291,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(A_102,B_103)
      | ~ m1_subset_1(A_102,k1_zfmisc_1(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_308,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_104,c_291])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_314,plain,(
    k3_xboole_0('#skF_7',u1_struct_0('#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_308,c_54])).

tff(c_1114,plain,(
    ! [D_152,B_153,A_154] :
      ( r2_hidden(D_152,B_153)
      | ~ r2_hidden(D_152,k3_xboole_0(A_154,B_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1133,plain,(
    ! [D_155] :
      ( r2_hidden(D_155,u1_struct_0('#skF_6'))
      | ~ r2_hidden(D_155,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_1114])).

tff(c_1138,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_1,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1133,c_4])).

tff(c_11135,plain,(
    ! [B_407] : r1_tarski(k4_xboole_0('#skF_7',B_407),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10914,c_1138])).

tff(c_17257,plain,(
    ! [B_521] : k3_xboole_0(k4_xboole_0('#skF_7',B_521),u1_struct_0('#skF_6')) = k4_xboole_0('#skF_7',B_521) ),
    inference(resolution,[status(thm)],[c_11135,c_54])).

tff(c_5911,plain,(
    ! [A_300,B_301] : m1_subset_1(k3_subset_1(A_300,k4_xboole_0(A_300,B_301)),k1_zfmisc_1(A_300)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5869,c_117])).

tff(c_13412,plain,(
    ! [A_451,B_452] : m1_subset_1(k3_xboole_0(A_451,B_452),k1_zfmisc_1(A_451)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13115,c_5911])).

tff(c_13515,plain,(
    ! [A_108,B_109] : m1_subset_1(k3_xboole_0(A_108,B_109),k1_zfmisc_1(B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_13412])).

tff(c_17510,plain,(
    ! [B_522] : m1_subset_1(k4_xboole_0('#skF_7',B_522),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17257,c_13515])).

tff(c_94,plain,(
    ! [A_61,B_62] :
      ( v3_pre_topc(k1_tops_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_17520,plain,(
    ! [B_522] :
      ( v3_pre_topc(k1_tops_1('#skF_6',k4_xboole_0('#skF_7',B_522)),'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_17510,c_94])).

tff(c_18147,plain,(
    ! [B_528] : v3_pre_topc(k1_tops_1('#skF_6',k4_xboole_0('#skF_7',B_528)),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_17520])).

tff(c_18161,plain,(
    v3_pre_topc(k1_tops_1('#skF_6',k1_tops_1('#skF_6','#skF_7')),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7663,c_18147])).

tff(c_97710,plain,(
    v3_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97634,c_97634,c_18161])).

tff(c_97752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_97710])).

tff(c_97753,plain,(
    k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),'#skF_7') != k2_tops_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_100827,plain,(
    ! [A_1374,B_1375,C_1376] :
      ( k7_subset_1(A_1374,B_1375,C_1376) = k4_xboole_0(B_1375,C_1376)
      | ~ m1_subset_1(B_1375,k1_zfmisc_1(A_1374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_100851,plain,(
    ! [C_1376] : k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',C_1376) = k4_xboole_0('#skF_7',C_1376) ),
    inference(resolution,[status(thm)],[c_104,c_100827])).

tff(c_105068,plain,(
    ! [A_1492,B_1493] :
      ( k7_subset_1(u1_struct_0(A_1492),B_1493,k2_tops_1(A_1492,B_1493)) = k1_tops_1(A_1492,B_1493)
      | ~ m1_subset_1(B_1493,k1_zfmisc_1(u1_struct_0(A_1492)))
      | ~ l1_pre_topc(A_1492) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_105098,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_105068])).

tff(c_105117,plain,(
    k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_100851,c_105098])).

tff(c_98275,plain,(
    ! [B_1289,A_1290] :
      ( B_1289 = A_1290
      | ~ r1_tarski(B_1289,A_1290)
      | ~ r1_tarski(A_1290,B_1289) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98286,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,k4_xboole_0(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_56,c_98275])).

tff(c_105169,plain,
    ( k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_tops_1('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105117,c_98286])).

tff(c_105209,plain,
    ( k1_tops_1('#skF_6','#skF_7') = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_tops_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105117,c_105169])).

tff(c_106204,plain,(
    ~ r1_tarski('#skF_7',k1_tops_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_105209])).

tff(c_97754,plain,(
    v3_pre_topc('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_50,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107464,plain,(
    ! [B_1542,A_1543,C_1544] :
      ( r1_tarski(B_1542,k1_tops_1(A_1543,C_1544))
      | ~ r1_tarski(B_1542,C_1544)
      | ~ v3_pre_topc(B_1542,A_1543)
      | ~ m1_subset_1(C_1544,k1_zfmisc_1(u1_struct_0(A_1543)))
      | ~ m1_subset_1(B_1542,k1_zfmisc_1(u1_struct_0(A_1543)))
      | ~ l1_pre_topc(A_1543) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_107500,plain,(
    ! [B_1542] :
      ( r1_tarski(B_1542,k1_tops_1('#skF_6','#skF_7'))
      | ~ r1_tarski(B_1542,'#skF_7')
      | ~ v3_pre_topc(B_1542,'#skF_6')
      | ~ m1_subset_1(B_1542,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_104,c_107464])).

tff(c_107525,plain,(
    ! [B_1545] :
      ( r1_tarski(B_1545,k1_tops_1('#skF_6','#skF_7'))
      | ~ r1_tarski(B_1545,'#skF_7')
      | ~ v3_pre_topc(B_1545,'#skF_6')
      | ~ m1_subset_1(B_1545,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_107500])).

tff(c_107575,plain,
    ( r1_tarski('#skF_7',k1_tops_1('#skF_6','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_107525])).

tff(c_107596,plain,(
    r1_tarski('#skF_7',k1_tops_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97754,c_50,c_107575])).

tff(c_107598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106204,c_107596])).

tff(c_107599,plain,(
    k1_tops_1('#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_105209])).

tff(c_96,plain,(
    ! [A_63,B_65] :
      ( k7_subset_1(u1_struct_0(A_63),k2_pre_topc(A_63,B_65),k1_tops_1(A_63,B_65)) = k2_tops_1(A_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_107626,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),'#skF_7') = k2_tops_1('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_107599,c_96])).

tff(c_107630,plain,(
    k7_subset_1(u1_struct_0('#skF_6'),k2_pre_topc('#skF_6','#skF_7'),'#skF_7') = k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_107626])).

tff(c_107632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97753,c_107630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 10:35:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.76/23.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.91/23.49  
% 33.91/23.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.91/23.49  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 33.91/23.49  
% 33.91/23.49  %Foreground sorts:
% 33.91/23.49  
% 33.91/23.49  
% 33.91/23.49  %Background operators:
% 33.91/23.49  
% 33.91/23.49  
% 33.91/23.49  %Foreground operators:
% 33.91/23.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 33.91/23.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.91/23.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 33.91/23.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 33.91/23.49  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 33.91/23.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.91/23.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 33.91/23.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 33.91/23.49  tff('#skF_7', type, '#skF_7': $i).
% 33.91/23.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 33.91/23.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.91/23.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 33.91/23.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 33.91/23.49  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 33.91/23.49  tff('#skF_6', type, '#skF_6': $i).
% 33.91/23.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 33.91/23.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 33.91/23.49  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 33.91/23.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 33.91/23.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.91/23.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.91/23.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 33.91/23.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 33.91/23.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.91/23.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 33.91/23.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 33.91/23.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 33.91/23.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 33.91/23.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 33.91/23.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 33.91/23.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.91/23.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 33.91/23.49  
% 34.01/23.52  tff(f_174, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 34.01/23.52  tff(f_77, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 34.01/23.52  tff(f_103, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 34.01/23.52  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 34.01/23.52  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 34.01/23.52  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 34.01/23.52  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 34.01/23.52  tff(f_75, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 34.01/23.52  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 34.01/23.52  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 34.01/23.52  tff(f_162, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 34.01/23.52  tff(f_119, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 34.01/23.52  tff(f_53, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 34.01/23.52  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 34.01/23.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 34.01/23.52  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 34.01/23.52  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 34.01/23.52  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 34.01/23.52  tff(f_107, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 34.01/23.52  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 34.01/23.52  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 34.01/23.52  tff(f_95, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 34.01/23.52  tff(f_89, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 34.01/23.52  tff(f_127, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 34.01/23.52  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 34.01/23.52  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 34.01/23.52  tff(c_110, plain, (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')!=k2_tops_1('#skF_6', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 34.01/23.52  tff(c_165, plain, (~v3_pre_topc('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_110])).
% 34.01/23.52  tff(c_66, plain, (![B_35, A_34]: (k2_tarski(B_35, A_34)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.01/23.52  tff(c_319, plain, (![A_104, B_105]: (k1_setfam_1(k2_tarski(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 34.01/23.52  tff(c_339, plain, (![A_108, B_109]: (k1_setfam_1(k2_tarski(A_108, B_109))=k3_xboole_0(B_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_66, c_319])).
% 34.01/23.52  tff(c_84, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_103])).
% 34.01/23.52  tff(c_362, plain, (![B_110, A_111]: (k3_xboole_0(B_110, A_111)=k3_xboole_0(A_111, B_110))), inference(superposition, [status(thm), theory('equality')], [c_339, c_84])).
% 34.01/23.52  tff(c_166, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k2_xboole_0(A_87, B_88))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.01/23.52  tff(c_56, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.01/23.52  tff(c_171, plain, (![A_87]: (r1_tarski(k1_xboole_0, A_87))), inference(superposition, [status(thm), theory('equality')], [c_166, c_56])).
% 34.01/23.52  tff(c_240, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 34.01/23.52  tff(c_250, plain, (![A_87]: (k3_xboole_0(k1_xboole_0, A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_171, c_240])).
% 34.01/23.52  tff(c_378, plain, (![B_110]: (k3_xboole_0(B_110, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_362, c_250])).
% 34.01/23.52  tff(c_58, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_69])).
% 34.01/23.52  tff(c_547, plain, (![A_125, B_126]: (k2_xboole_0(k3_xboole_0(A_125, B_126), k4_xboole_0(A_125, B_126))=A_125)), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.01/23.52  tff(c_577, plain, (![A_28]: (k2_xboole_0(k3_xboole_0(A_28, k1_xboole_0), A_28)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_58, c_547])).
% 34.01/23.52  tff(c_599, plain, (![A_127]: (k2_xboole_0(k1_xboole_0, A_127)=A_127)), inference(demodulation, [status(thm), theory('equality')], [c_378, c_577])).
% 34.01/23.52  tff(c_276, plain, (![A_100, B_101]: (k3_tarski(k2_tarski(A_100, B_101))=k2_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_79])).
% 34.01/23.52  tff(c_485, plain, (![B_121, A_122]: (k3_tarski(k2_tarski(B_121, A_122))=k2_xboole_0(A_122, B_121))), inference(superposition, [status(thm), theory('equality')], [c_66, c_276])).
% 34.01/23.52  tff(c_68, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 34.01/23.52  tff(c_491, plain, (![B_121, A_122]: (k2_xboole_0(B_121, A_122)=k2_xboole_0(A_122, B_121))), inference(superposition, [status(thm), theory('equality')], [c_485, c_68])).
% 34.01/23.52  tff(c_605, plain, (![A_127]: (k2_xboole_0(A_127, k1_xboole_0)=A_127)), inference(superposition, [status(thm), theory('equality')], [c_599, c_491])).
% 34.01/23.52  tff(c_106, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 34.01/23.52  tff(c_104, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 34.01/23.52  tff(c_2463, plain, (![A_205, B_206, C_207]: (k7_subset_1(A_205, B_206, C_207)=k4_xboole_0(B_206, C_207) | ~m1_subset_1(B_206, k1_zfmisc_1(A_205)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 34.01/23.52  tff(c_2487, plain, (![C_207]: (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', C_207)=k4_xboole_0('#skF_7', C_207))), inference(resolution, [status(thm)], [c_104, c_2463])).
% 34.01/23.52  tff(c_7606, plain, (![A_342, B_343]: (k7_subset_1(u1_struct_0(A_342), B_343, k2_tops_1(A_342, B_343))=k1_tops_1(A_342, B_343) | ~m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0(A_342))) | ~l1_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_162])).
% 34.01/23.52  tff(c_7642, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_7606])).
% 34.01/23.52  tff(c_7663, plain, (k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2487, c_7642])).
% 34.01/23.52  tff(c_4191, plain, (![A_245, B_246]: (m1_subset_1(k2_pre_topc(A_245, B_246), k1_zfmisc_1(u1_struct_0(A_245))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_119])).
% 34.01/23.52  tff(c_80, plain, (![A_48, B_49, C_50]: (k7_subset_1(A_48, B_49, C_50)=k4_xboole_0(B_49, C_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 34.01/23.52  tff(c_25287, plain, (![A_618, B_619, C_620]: (k7_subset_1(u1_struct_0(A_618), k2_pre_topc(A_618, B_619), C_620)=k4_xboole_0(k2_pre_topc(A_618, B_619), C_620) | ~m1_subset_1(B_619, k1_zfmisc_1(u1_struct_0(A_618))) | ~l1_pre_topc(A_618))), inference(resolution, [status(thm)], [c_4191, c_80])).
% 34.01/23.52  tff(c_25338, plain, (![C_620]: (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), C_620)=k4_xboole_0(k2_pre_topc('#skF_6', '#skF_7'), C_620) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_104, c_25287])).
% 34.01/23.52  tff(c_25382, plain, (![C_621]: (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), C_621)=k4_xboole_0(k2_pre_topc('#skF_6', '#skF_7'), C_621))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_25338])).
% 34.01/23.52  tff(c_116, plain, (v3_pre_topc('#skF_7', '#skF_6') | k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')=k2_tops_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_174])).
% 34.01/23.52  tff(c_271, plain, (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')=k2_tops_1('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_165, c_116])).
% 34.01/23.52  tff(c_25396, plain, (k4_xboole_0(k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')=k2_tops_1('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_25382, c_271])).
% 34.01/23.52  tff(c_345, plain, (![B_109, A_108]: (k3_xboole_0(B_109, A_108)=k3_xboole_0(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_339, c_84])).
% 34.01/23.52  tff(c_628, plain, (![A_128]: (k2_xboole_0(A_128, k1_xboole_0)=A_128)), inference(superposition, [status(thm), theory('equality')], [c_599, c_491])).
% 34.01/23.52  tff(c_60, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.01/23.52  tff(c_644, plain, (![A_128]: (k4_xboole_0(A_128, A_128)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_628, c_60])).
% 34.01/23.52  tff(c_44, plain, (![A_18]: (k3_xboole_0(A_18, A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 34.01/23.52  tff(c_1018, plain, (![A_143, B_144]: (k5_xboole_0(A_143, k3_xboole_0(A_143, B_144))=k4_xboole_0(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_61])).
% 34.01/23.52  tff(c_1042, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k4_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1018])).
% 34.01/23.52  tff(c_1048, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_644, c_1042])).
% 34.01/23.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.01/23.52  tff(c_2594, plain, (![D_213, A_214, B_215]: (r2_hidden(D_213, k4_xboole_0(A_214, B_215)) | r2_hidden(D_213, B_215) | ~r2_hidden(D_213, A_214))), inference(cnfTransformation, [status(thm)], [f_51])).
% 34.01/23.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.01/23.52  tff(c_27429, plain, (![A_641, A_642, B_643]: (r1_tarski(A_641, k4_xboole_0(A_642, B_643)) | r2_hidden('#skF_1'(A_641, k4_xboole_0(A_642, B_643)), B_643) | ~r2_hidden('#skF_1'(A_641, k4_xboole_0(A_642, B_643)), A_642))), inference(resolution, [status(thm)], [c_2594, c_4])).
% 34.01/23.52  tff(c_94901, plain, (![A_1233, B_1234]: (r2_hidden('#skF_1'(A_1233, k4_xboole_0(A_1233, B_1234)), B_1234) | r1_tarski(A_1233, k4_xboole_0(A_1233, B_1234)))), inference(resolution, [status(thm)], [c_6, c_27429])).
% 34.01/23.52  tff(c_1139, plain, (![A_156, B_157]: (r2_hidden('#skF_1'(A_156, B_157), A_156) | r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.01/23.52  tff(c_28, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 34.01/23.52  tff(c_1169, plain, (![A_12, B_13, B_157]: (~r2_hidden('#skF_1'(k4_xboole_0(A_12, B_13), B_157), B_13) | r1_tarski(k4_xboole_0(A_12, B_13), B_157))), inference(resolution, [status(thm)], [c_1139, c_28])).
% 34.01/23.52  tff(c_95392, plain, (![A_1235, B_1236]: (r1_tarski(k4_xboole_0(A_1235, B_1236), k4_xboole_0(k4_xboole_0(A_1235, B_1236), B_1236)))), inference(resolution, [status(thm)], [c_94901, c_1169])).
% 34.01/23.52  tff(c_668, plain, (![B_129, A_130]: (B_129=A_130 | ~r1_tarski(B_129, A_130) | ~r1_tarski(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_59])).
% 34.01/23.52  tff(c_679, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_56, c_668])).
% 34.01/23.52  tff(c_95878, plain, (![A_1237, B_1238]: (k4_xboole_0(k4_xboole_0(A_1237, B_1238), B_1238)=k4_xboole_0(A_1237, B_1238))), inference(resolution, [status(thm)], [c_95392, c_679])).
% 34.01/23.52  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.01/23.52  tff(c_11624, plain, (![A_423, B_424, B_425]: (r2_hidden('#skF_1'(k3_xboole_0(A_423, B_424), B_425), A_423) | r1_tarski(k3_xboole_0(A_423, B_424), B_425))), inference(resolution, [status(thm)], [c_1139, c_12])).
% 34.01/23.52  tff(c_11831, plain, (![A_423, B_424]: (r1_tarski(k3_xboole_0(A_423, B_424), A_423))), inference(resolution, [status(thm)], [c_11624, c_4])).
% 34.01/23.52  tff(c_52, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 34.01/23.52  tff(c_588, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_378, c_577])).
% 34.01/23.52  tff(c_747, plain, (![A_133, B_134]: (k4_xboole_0(k3_xboole_0(A_133, B_134), A_133)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_547, c_60])).
% 34.01/23.52  tff(c_64, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.01/23.52  tff(c_752, plain, (![A_133, B_134]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_133, B_134), A_133), k1_xboole_0)=k3_xboole_0(A_133, B_134))), inference(superposition, [status(thm), theory('equality')], [c_747, c_64])).
% 34.01/23.52  tff(c_1854, plain, (![A_191, B_192]: (k3_xboole_0(A_191, k3_xboole_0(A_191, B_192))=k3_xboole_0(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_491, c_345, c_752])).
% 34.01/23.52  tff(c_1872, plain, (![A_191, B_192]: (k5_xboole_0(A_191, k3_xboole_0(A_191, B_192))=k4_xboole_0(A_191, k3_xboole_0(A_191, B_192)))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_52])).
% 34.01/23.52  tff(c_1933, plain, (![A_191, B_192]: (k4_xboole_0(A_191, k3_xboole_0(A_191, B_192))=k4_xboole_0(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1872])).
% 34.01/23.52  tff(c_11859, plain, (![A_426, B_427]: (r1_tarski(k3_xboole_0(A_426, B_427), A_426))), inference(resolution, [status(thm)], [c_11624, c_4])).
% 34.01/23.52  tff(c_88, plain, (![A_54, B_55]: (m1_subset_1(A_54, k1_zfmisc_1(B_55)) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_107])).
% 34.01/23.52  tff(c_1962, plain, (![A_195, B_196]: (k4_xboole_0(A_195, B_196)=k3_subset_1(A_195, B_196) | ~m1_subset_1(B_196, k1_zfmisc_1(A_195)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 34.01/23.52  tff(c_1983, plain, (![B_55, A_54]: (k4_xboole_0(B_55, A_54)=k3_subset_1(B_55, A_54) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_88, c_1962])).
% 34.01/23.52  tff(c_11871, plain, (![A_426, B_427]: (k4_xboole_0(A_426, k3_xboole_0(A_426, B_427))=k3_subset_1(A_426, k3_xboole_0(A_426, B_427)))), inference(resolution, [status(thm)], [c_11859, c_1983])).
% 34.01/23.52  tff(c_13010, plain, (![A_445, B_446]: (k3_subset_1(A_445, k3_xboole_0(A_445, B_446))=k4_xboole_0(A_445, B_446))), inference(demodulation, [status(thm), theory('equality')], [c_1933, c_11871])).
% 34.01/23.52  tff(c_1787, plain, (![A_187, B_188]: (k3_subset_1(A_187, k3_subset_1(A_187, B_188))=B_188 | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 34.01/23.52  tff(c_1798, plain, (![B_55, A_54]: (k3_subset_1(B_55, k3_subset_1(B_55, A_54))=A_54 | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_88, c_1787])).
% 34.01/23.52  tff(c_13020, plain, (![A_445, B_446]: (k3_subset_1(A_445, k4_xboole_0(A_445, B_446))=k3_xboole_0(A_445, B_446) | ~r1_tarski(k3_xboole_0(A_445, B_446), A_445))), inference(superposition, [status(thm), theory('equality')], [c_13010, c_1798])).
% 34.01/23.52  tff(c_13115, plain, (![A_445, B_446]: (k3_subset_1(A_445, k4_xboole_0(A_445, B_446))=k3_xboole_0(A_445, B_446))), inference(demodulation, [status(thm), theory('equality')], [c_11831, c_13020])).
% 34.01/23.52  tff(c_78, plain, (![A_46, B_47]: (k6_subset_1(A_46, B_47)=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_95])).
% 34.01/23.52  tff(c_74, plain, (![A_42, B_43]: (m1_subset_1(k6_subset_1(A_42, B_43), k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 34.01/23.52  tff(c_117, plain, (![A_42, B_43]: (m1_subset_1(k4_xboole_0(A_42, B_43), k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74])).
% 34.01/23.52  tff(c_1986, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_subset_1(A_42, k4_xboole_0(A_42, B_43)))), inference(resolution, [status(thm)], [c_117, c_1962])).
% 34.01/23.52  tff(c_251, plain, (![A_26, B_27]: (k3_xboole_0(k4_xboole_0(A_26, B_27), A_26)=k4_xboole_0(A_26, B_27))), inference(resolution, [status(thm)], [c_56, c_240])).
% 34.01/23.52  tff(c_1479, plain, (![A_170, B_171]: (k5_xboole_0(A_170, k3_xboole_0(B_171, A_170))=k4_xboole_0(A_170, B_171))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1018])).
% 34.01/23.52  tff(c_1492, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k4_xboole_0(A_26, k4_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_251, c_1479])).
% 34.01/23.52  tff(c_9420, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_subset_1(A_26, k4_xboole_0(A_26, B_27)))), inference(demodulation, [status(thm), theory('equality')], [c_1986, c_1492])).
% 34.01/23.52  tff(c_13285, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_13115, c_9420])).
% 34.01/23.52  tff(c_96058, plain, (![A_1237, B_1238]: (k5_xboole_0(k4_xboole_0(A_1237, B_1238), k4_xboole_0(A_1237, B_1238))=k3_xboole_0(k4_xboole_0(A_1237, B_1238), B_1238))), inference(superposition, [status(thm), theory('equality')], [c_95878, c_13285])).
% 34.01/23.52  tff(c_96434, plain, (![B_1239, A_1240]: (k3_xboole_0(B_1239, k4_xboole_0(A_1240, B_1239))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_1048, c_96058])).
% 34.01/23.52  tff(c_96934, plain, (k3_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25396, c_96434])).
% 34.01/23.52  tff(c_1381, plain, (![A_167, B_168]: (k3_xboole_0(k4_xboole_0(A_167, B_168), A_167)=k4_xboole_0(A_167, B_168))), inference(resolution, [status(thm)], [c_56, c_240])).
% 34.01/23.52  tff(c_1445, plain, (![A_108, B_168]: (k3_xboole_0(A_108, k4_xboole_0(A_108, B_168))=k4_xboole_0(A_108, B_168))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1381])).
% 34.01/23.52  tff(c_5869, plain, (![A_300, B_301]: (k4_xboole_0(A_300, k4_xboole_0(A_300, B_301))=k3_subset_1(A_300, k4_xboole_0(A_300, B_301)))), inference(resolution, [status(thm)], [c_117, c_1962])).
% 34.01/23.52  tff(c_5905, plain, (![A_300, B_301]: (k2_xboole_0(k3_xboole_0(A_300, k4_xboole_0(A_300, B_301)), k3_subset_1(A_300, k4_xboole_0(A_300, B_301)))=A_300)), inference(superposition, [status(thm), theory('equality')], [c_5869, c_64])).
% 34.01/23.52  tff(c_5981, plain, (![A_300, B_301]: (k2_xboole_0(k4_xboole_0(A_300, B_301), k3_subset_1(A_300, k4_xboole_0(A_300, B_301)))=A_300)), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_5905])).
% 34.01/23.52  tff(c_13286, plain, (![A_300, B_301]: (k2_xboole_0(k4_xboole_0(A_300, B_301), k3_xboole_0(A_300, B_301))=A_300)), inference(demodulation, [status(thm), theory('equality')], [c_13115, c_5981])).
% 34.01/23.52  tff(c_97445, plain, (k2_xboole_0(k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7')), k1_xboole_0)='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_96934, c_13286])).
% 34.01/23.52  tff(c_97634, plain, (k1_tops_1('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_605, c_7663, c_97445])).
% 34.01/23.52  tff(c_108, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 34.01/23.52  tff(c_30, plain, (![D_17, A_12, B_13]: (r2_hidden(D_17, A_12) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 34.01/23.52  tff(c_10914, plain, (![A_404, B_405, B_406]: (r2_hidden('#skF_1'(k4_xboole_0(A_404, B_405), B_406), A_404) | r1_tarski(k4_xboole_0(A_404, B_405), B_406))), inference(resolution, [status(thm)], [c_1139, c_30])).
% 34.01/23.52  tff(c_291, plain, (![A_102, B_103]: (r1_tarski(A_102, B_103) | ~m1_subset_1(A_102, k1_zfmisc_1(B_103)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 34.01/23.52  tff(c_308, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_104, c_291])).
% 34.01/23.52  tff(c_54, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 34.01/23.52  tff(c_314, plain, (k3_xboole_0('#skF_7', u1_struct_0('#skF_6'))='#skF_7'), inference(resolution, [status(thm)], [c_308, c_54])).
% 34.01/23.52  tff(c_1114, plain, (![D_152, B_153, A_154]: (r2_hidden(D_152, B_153) | ~r2_hidden(D_152, k3_xboole_0(A_154, B_153)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.01/23.52  tff(c_1133, plain, (![D_155]: (r2_hidden(D_155, u1_struct_0('#skF_6')) | ~r2_hidden(D_155, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_1114])).
% 34.01/23.52  tff(c_1138, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'(A_1, u1_struct_0('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_1133, c_4])).
% 34.01/23.52  tff(c_11135, plain, (![B_407]: (r1_tarski(k4_xboole_0('#skF_7', B_407), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_10914, c_1138])).
% 34.01/23.52  tff(c_17257, plain, (![B_521]: (k3_xboole_0(k4_xboole_0('#skF_7', B_521), u1_struct_0('#skF_6'))=k4_xboole_0('#skF_7', B_521))), inference(resolution, [status(thm)], [c_11135, c_54])).
% 34.01/23.52  tff(c_5911, plain, (![A_300, B_301]: (m1_subset_1(k3_subset_1(A_300, k4_xboole_0(A_300, B_301)), k1_zfmisc_1(A_300)))), inference(superposition, [status(thm), theory('equality')], [c_5869, c_117])).
% 34.01/23.52  tff(c_13412, plain, (![A_451, B_452]: (m1_subset_1(k3_xboole_0(A_451, B_452), k1_zfmisc_1(A_451)))), inference(demodulation, [status(thm), theory('equality')], [c_13115, c_5911])).
% 34.01/23.52  tff(c_13515, plain, (![A_108, B_109]: (m1_subset_1(k3_xboole_0(A_108, B_109), k1_zfmisc_1(B_109)))), inference(superposition, [status(thm), theory('equality')], [c_345, c_13412])).
% 34.01/23.52  tff(c_17510, plain, (![B_522]: (m1_subset_1(k4_xboole_0('#skF_7', B_522), k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_17257, c_13515])).
% 34.01/23.52  tff(c_94, plain, (![A_61, B_62]: (v3_pre_topc(k1_tops_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_127])).
% 34.01/23.52  tff(c_17520, plain, (![B_522]: (v3_pre_topc(k1_tops_1('#skF_6', k4_xboole_0('#skF_7', B_522)), '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_17510, c_94])).
% 34.01/23.52  tff(c_18147, plain, (![B_528]: (v3_pre_topc(k1_tops_1('#skF_6', k4_xboole_0('#skF_7', B_528)), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_17520])).
% 34.01/23.52  tff(c_18161, plain, (v3_pre_topc(k1_tops_1('#skF_6', k1_tops_1('#skF_6', '#skF_7')), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7663, c_18147])).
% 34.01/23.52  tff(c_97710, plain, (v3_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_97634, c_97634, c_18161])).
% 34.01/23.52  tff(c_97752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_97710])).
% 34.01/23.52  tff(c_97753, plain, (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')!=k2_tops_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_110])).
% 34.01/23.52  tff(c_100827, plain, (![A_1374, B_1375, C_1376]: (k7_subset_1(A_1374, B_1375, C_1376)=k4_xboole_0(B_1375, C_1376) | ~m1_subset_1(B_1375, k1_zfmisc_1(A_1374)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 34.01/23.52  tff(c_100851, plain, (![C_1376]: (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', C_1376)=k4_xboole_0('#skF_7', C_1376))), inference(resolution, [status(thm)], [c_104, c_100827])).
% 34.01/23.52  tff(c_105068, plain, (![A_1492, B_1493]: (k7_subset_1(u1_struct_0(A_1492), B_1493, k2_tops_1(A_1492, B_1493))=k1_tops_1(A_1492, B_1493) | ~m1_subset_1(B_1493, k1_zfmisc_1(u1_struct_0(A_1492))) | ~l1_pre_topc(A_1492))), inference(cnfTransformation, [status(thm)], [f_162])).
% 34.01/23.52  tff(c_105098, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_104, c_105068])).
% 34.01/23.52  tff(c_105117, plain, (k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_100851, c_105098])).
% 34.01/23.52  tff(c_98275, plain, (![B_1289, A_1290]: (B_1289=A_1290 | ~r1_tarski(B_1289, A_1290) | ~r1_tarski(A_1290, B_1289))), inference(cnfTransformation, [status(thm)], [f_59])).
% 34.01/23.52  tff(c_98286, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_56, c_98275])).
% 34.01/23.52  tff(c_105169, plain, (k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))='#skF_7' | ~r1_tarski('#skF_7', k1_tops_1('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_105117, c_98286])).
% 34.01/23.52  tff(c_105209, plain, (k1_tops_1('#skF_6', '#skF_7')='#skF_7' | ~r1_tarski('#skF_7', k1_tops_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_105117, c_105169])).
% 34.01/23.52  tff(c_106204, plain, (~r1_tarski('#skF_7', k1_tops_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_105209])).
% 34.01/23.52  tff(c_97754, plain, (v3_pre_topc('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_110])).
% 34.01/23.52  tff(c_50, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 34.01/23.52  tff(c_107464, plain, (![B_1542, A_1543, C_1544]: (r1_tarski(B_1542, k1_tops_1(A_1543, C_1544)) | ~r1_tarski(B_1542, C_1544) | ~v3_pre_topc(B_1542, A_1543) | ~m1_subset_1(C_1544, k1_zfmisc_1(u1_struct_0(A_1543))) | ~m1_subset_1(B_1542, k1_zfmisc_1(u1_struct_0(A_1543))) | ~l1_pre_topc(A_1543))), inference(cnfTransformation, [status(thm)], [f_148])).
% 34.01/23.52  tff(c_107500, plain, (![B_1542]: (r1_tarski(B_1542, k1_tops_1('#skF_6', '#skF_7')) | ~r1_tarski(B_1542, '#skF_7') | ~v3_pre_topc(B_1542, '#skF_6') | ~m1_subset_1(B_1542, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_104, c_107464])).
% 34.01/23.52  tff(c_107525, plain, (![B_1545]: (r1_tarski(B_1545, k1_tops_1('#skF_6', '#skF_7')) | ~r1_tarski(B_1545, '#skF_7') | ~v3_pre_topc(B_1545, '#skF_6') | ~m1_subset_1(B_1545, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_107500])).
% 34.01/23.52  tff(c_107575, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_6', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_104, c_107525])).
% 34.01/23.52  tff(c_107596, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97754, c_50, c_107575])).
% 34.01/23.52  tff(c_107598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106204, c_107596])).
% 34.01/23.52  tff(c_107599, plain, (k1_tops_1('#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_105209])).
% 34.01/23.52  tff(c_96, plain, (![A_63, B_65]: (k7_subset_1(u1_struct_0(A_63), k2_pre_topc(A_63, B_65), k1_tops_1(A_63, B_65))=k2_tops_1(A_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_134])).
% 34.01/23.52  tff(c_107626, plain, (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')=k2_tops_1('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_107599, c_96])).
% 34.01/23.52  tff(c_107630, plain, (k7_subset_1(u1_struct_0('#skF_6'), k2_pre_topc('#skF_6', '#skF_7'), '#skF_7')=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_107626])).
% 34.01/23.52  tff(c_107632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97753, c_107630])).
% 34.01/23.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.01/23.52  
% 34.01/23.52  Inference rules
% 34.01/23.52  ----------------------
% 34.01/23.52  #Ref     : 0
% 34.01/23.52  #Sup     : 25937
% 34.01/23.52  #Fact    : 0
% 34.01/23.52  #Define  : 0
% 34.01/23.52  #Split   : 24
% 34.01/23.52  #Chain   : 0
% 34.01/23.52  #Close   : 0
% 34.01/23.52  
% 34.01/23.52  Ordering : KBO
% 34.01/23.52  
% 34.01/23.52  Simplification rules
% 34.01/23.52  ----------------------
% 34.01/23.52  #Subsume      : 4839
% 34.01/23.52  #Demod        : 29941
% 34.01/23.52  #Tautology    : 8371
% 34.01/23.52  #SimpNegUnit  : 208
% 34.01/23.52  #BackRed      : 438
% 34.01/23.52  
% 34.01/23.52  #Partial instantiations: 0
% 34.01/23.52  #Strategies tried      : 1
% 34.01/23.52  
% 34.01/23.52  Timing (in seconds)
% 34.01/23.52  ----------------------
% 34.01/23.52  Preprocessing        : 0.38
% 34.01/23.52  Parsing              : 0.21
% 34.01/23.52  CNF conversion       : 0.03
% 34.01/23.52  Main loop            : 22.29
% 34.01/23.52  Inferencing          : 2.53
% 34.01/23.52  Reduction            : 12.30
% 34.01/23.52  Demodulation         : 10.83
% 34.01/23.52  BG Simplification    : 0.31
% 34.01/23.52  Subsumption          : 6.00
% 34.01/23.52  Abstraction          : 0.53
% 34.01/23.52  MUC search           : 0.00
% 34.01/23.52  Cooper               : 0.00
% 34.01/23.52  Total                : 22.74
% 34.01/23.52  Index Insertion      : 0.00
% 34.01/23.52  Index Deletion       : 0.00
% 34.01/23.52  Index Matching       : 0.00
% 34.01/23.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
