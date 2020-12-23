%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:45 EST 2020

% Result     : Theorem 16.56s
% Output     : CNFRefutation 16.56s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 163 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 347 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_37,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_10,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,k4_xboole_0(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_252,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(A_90,k4_xboole_0(B_91,C_92))
      | ~ r1_xboole_0(A_90,C_92)
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_842,plain,(
    ! [A_171,B_172,C_173,A_174] :
      ( r1_tarski(A_171,k4_xboole_0(B_172,C_173))
      | ~ r1_tarski(A_171,A_174)
      | ~ r1_xboole_0(A_174,C_173)
      | ~ r1_tarski(A_174,B_172) ) ),
    inference(resolution,[status(thm)],[c_252,c_4])).

tff(c_2254,plain,(
    ! [A_266,B_267,B_268,C_269] :
      ( r1_tarski(k4_xboole_0(A_266,B_267),k4_xboole_0(B_268,C_269))
      | ~ r1_xboole_0(A_266,C_269)
      | ~ r1_tarski(A_266,B_268) ) ),
    inference(resolution,[status(thm)],[c_6,c_842])).

tff(c_59,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_52,A_6,B_7] :
      ( r1_tarski(A_52,A_6)
      | ~ r1_tarski(A_52,k4_xboole_0(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_2311,plain,(
    ! [A_270,B_271,B_272,C_273] :
      ( r1_tarski(k4_xboole_0(A_270,B_271),B_272)
      | ~ r1_xboole_0(A_270,C_273)
      | ~ r1_tarski(A_270,B_272) ) ),
    inference(resolution,[status(thm)],[c_2254,c_68])).

tff(c_2846,plain,(
    ! [A_284,B_285,B_286,B_287] :
      ( r1_tarski(k4_xboole_0(A_284,B_285),B_286)
      | ~ r1_tarski(A_284,B_286)
      | ~ r1_tarski(A_284,B_287) ) ),
    inference(resolution,[status(thm)],[c_10,c_2311])).

tff(c_2965,plain,(
    ! [B_285,B_286] :
      ( r1_tarski(k4_xboole_0('#skF_2',B_285),B_286)
      | ~ r1_tarski('#skF_2',B_286) ) ),
    inference(resolution,[status(thm)],[c_44,c_2846])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_326,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k1_tops_1(A_103,B_104),B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_333,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_326])).

tff(c_340,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_333])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_334,plain,(
    ! [A_103,A_20] :
      ( r1_tarski(k1_tops_1(A_103,A_20),A_20)
      | ~ l1_pre_topc(A_103)
      | ~ r1_tarski(A_20,u1_struct_0(A_103)) ) ),
    inference(resolution,[status(thm)],[c_18,c_326])).

tff(c_51,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,k4_xboole_0(C_47,B_48))
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [C_47,B_48,A_46] :
      ( r1_xboole_0(k4_xboole_0(C_47,B_48),A_46)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_73,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_xboole_0(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_676,plain,(
    ! [A_145,A_146,C_147,B_148] :
      ( r1_xboole_0(A_145,A_146)
      | ~ r1_tarski(A_145,k4_xboole_0(C_147,B_148))
      | ~ r1_tarski(A_146,B_148) ) ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_31935,plain,(
    ! [A_1430,C_1431,B_1432,A_1433] :
      ( r1_xboole_0(k1_tops_1(A_1430,k4_xboole_0(C_1431,B_1432)),A_1433)
      | ~ r1_tarski(A_1433,B_1432)
      | ~ l1_pre_topc(A_1430)
      | ~ r1_tarski(k4_xboole_0(C_1431,B_1432),u1_struct_0(A_1430)) ) ),
    inference(resolution,[status(thm)],[c_334,c_676])).

tff(c_24,plain,(
    ! [A_27,B_31,C_33] :
      ( r1_tarski(k1_tops_1(A_27,B_31),k1_tops_1(A_27,C_33))
      | ~ r1_tarski(B_31,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(A_14,k4_xboole_0(B_15,C_16))
      | ~ r1_xboole_0(A_14,C_16)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_474,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(k1_tops_1(A_115,B_116),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1223,plain,(
    ! [A_198,B_199,C_200] :
      ( k7_subset_1(u1_struct_0(A_198),k1_tops_1(A_198,B_199),C_200) = k4_xboole_0(k1_tops_1(A_198,B_199),C_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_474,c_14])).

tff(c_1230,plain,(
    ! [C_200] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_200) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_200)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1223])).

tff(c_1237,plain,(
    ! [C_200] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_200) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1230])).

tff(c_193,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [C_84] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_84) = k4_xboole_0('#skF_2',C_84) ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_26,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_203,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_26])).

tff(c_1261,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_203])).

tff(c_1688,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_1261])).

tff(c_29745,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1688])).

tff(c_29748,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_29745])).

tff(c_29751,plain,(
    ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_6,c_29748])).

tff(c_29755,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_29751])).

tff(c_29758,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2965,c_29755])).

tff(c_29774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_29758])).

tff(c_29775,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1688])).

tff(c_31941,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_31935,c_29775])).

tff(c_31979,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_340,c_31941])).

tff(c_31996,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2965,c_31979])).

tff(c_32012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_31996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.56/9.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/9.43  
% 16.56/9.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/9.44  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 16.56/9.44  
% 16.56/9.44  %Foreground sorts:
% 16.56/9.44  
% 16.56/9.44  
% 16.56/9.44  %Background operators:
% 16.56/9.44  
% 16.56/9.44  
% 16.56/9.44  %Foreground operators:
% 16.56/9.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.56/9.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.56/9.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.56/9.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.56/9.44  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.56/9.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.56/9.44  tff('#skF_2', type, '#skF_2': $i).
% 16.56/9.44  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.56/9.44  tff('#skF_3', type, '#skF_3': $i).
% 16.56/9.44  tff('#skF_1', type, '#skF_1': $i).
% 16.56/9.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.56/9.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.56/9.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.56/9.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.56/9.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.56/9.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.56/9.44  
% 16.56/9.45  tff(f_99, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 16.56/9.45  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.56/9.45  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 16.56/9.45  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.56/9.45  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 16.56/9.45  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.56/9.45  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 16.56/9.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 16.56/9.45  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 16.56/9.45  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 16.56/9.45  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 16.56/9.45  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.56/9.45  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.56/9.45  tff(c_37, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.56/9.45  tff(c_44, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_37])).
% 16.56/9.45  tff(c_10, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, k4_xboole_0(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.56/9.45  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.56/9.45  tff(c_252, plain, (![A_90, B_91, C_92]: (r1_tarski(A_90, k4_xboole_0(B_91, C_92)) | ~r1_xboole_0(A_90, C_92) | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.56/9.45  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.56/9.45  tff(c_842, plain, (![A_171, B_172, C_173, A_174]: (r1_tarski(A_171, k4_xboole_0(B_172, C_173)) | ~r1_tarski(A_171, A_174) | ~r1_xboole_0(A_174, C_173) | ~r1_tarski(A_174, B_172))), inference(resolution, [status(thm)], [c_252, c_4])).
% 16.56/9.45  tff(c_2254, plain, (![A_266, B_267, B_268, C_269]: (r1_tarski(k4_xboole_0(A_266, B_267), k4_xboole_0(B_268, C_269)) | ~r1_xboole_0(A_266, C_269) | ~r1_tarski(A_266, B_268))), inference(resolution, [status(thm)], [c_6, c_842])).
% 16.56/9.45  tff(c_59, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.56/9.45  tff(c_68, plain, (![A_52, A_6, B_7]: (r1_tarski(A_52, A_6) | ~r1_tarski(A_52, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_6, c_59])).
% 16.56/9.45  tff(c_2311, plain, (![A_270, B_271, B_272, C_273]: (r1_tarski(k4_xboole_0(A_270, B_271), B_272) | ~r1_xboole_0(A_270, C_273) | ~r1_tarski(A_270, B_272))), inference(resolution, [status(thm)], [c_2254, c_68])).
% 16.56/9.45  tff(c_2846, plain, (![A_284, B_285, B_286, B_287]: (r1_tarski(k4_xboole_0(A_284, B_285), B_286) | ~r1_tarski(A_284, B_286) | ~r1_tarski(A_284, B_287))), inference(resolution, [status(thm)], [c_10, c_2311])).
% 16.56/9.45  tff(c_2965, plain, (![B_285, B_286]: (r1_tarski(k4_xboole_0('#skF_2', B_285), B_286) | ~r1_tarski('#skF_2', B_286))), inference(resolution, [status(thm)], [c_44, c_2846])).
% 16.56/9.45  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.56/9.45  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.56/9.45  tff(c_326, plain, (![A_103, B_104]: (r1_tarski(k1_tops_1(A_103, B_104), B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.56/9.45  tff(c_333, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_326])).
% 16.56/9.45  tff(c_340, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_333])).
% 16.56/9.45  tff(c_18, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.56/9.45  tff(c_334, plain, (![A_103, A_20]: (r1_tarski(k1_tops_1(A_103, A_20), A_20) | ~l1_pre_topc(A_103) | ~r1_tarski(A_20, u1_struct_0(A_103)))), inference(resolution, [status(thm)], [c_18, c_326])).
% 16.56/9.45  tff(c_51, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, k4_xboole_0(C_47, B_48)) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.56/9.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.56/9.45  tff(c_54, plain, (![C_47, B_48, A_46]: (r1_xboole_0(k4_xboole_0(C_47, B_48), A_46) | ~r1_tarski(A_46, B_48))), inference(resolution, [status(thm)], [c_51, c_2])).
% 16.56/9.45  tff(c_73, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, C_57) | ~r1_xboole_0(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.56/9.45  tff(c_676, plain, (![A_145, A_146, C_147, B_148]: (r1_xboole_0(A_145, A_146) | ~r1_tarski(A_145, k4_xboole_0(C_147, B_148)) | ~r1_tarski(A_146, B_148))), inference(resolution, [status(thm)], [c_54, c_73])).
% 16.56/9.45  tff(c_31935, plain, (![A_1430, C_1431, B_1432, A_1433]: (r1_xboole_0(k1_tops_1(A_1430, k4_xboole_0(C_1431, B_1432)), A_1433) | ~r1_tarski(A_1433, B_1432) | ~l1_pre_topc(A_1430) | ~r1_tarski(k4_xboole_0(C_1431, B_1432), u1_struct_0(A_1430)))), inference(resolution, [status(thm)], [c_334, c_676])).
% 16.56/9.45  tff(c_24, plain, (![A_27, B_31, C_33]: (r1_tarski(k1_tops_1(A_27, B_31), k1_tops_1(A_27, C_33)) | ~r1_tarski(B_31, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.56/9.45  tff(c_12, plain, (![A_14, B_15, C_16]: (r1_tarski(A_14, k4_xboole_0(B_15, C_16)) | ~r1_xboole_0(A_14, C_16) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.56/9.45  tff(c_474, plain, (![A_115, B_116]: (m1_subset_1(k1_tops_1(A_115, B_116), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.56/9.45  tff(c_14, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.56/9.45  tff(c_1223, plain, (![A_198, B_199, C_200]: (k7_subset_1(u1_struct_0(A_198), k1_tops_1(A_198, B_199), C_200)=k4_xboole_0(k1_tops_1(A_198, B_199), C_200) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_474, c_14])).
% 16.56/9.45  tff(c_1230, plain, (![C_200]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_200)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_200) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1223])).
% 16.56/9.45  tff(c_1237, plain, (![C_200]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_200)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_200))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1230])).
% 16.56/9.45  tff(c_193, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.56/9.45  tff(c_201, plain, (![C_84]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_84)=k4_xboole_0('#skF_2', C_84))), inference(resolution, [status(thm)], [c_30, c_193])).
% 16.56/9.45  tff(c_26, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.56/9.45  tff(c_203, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_26])).
% 16.56/9.45  tff(c_1261, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_203])).
% 16.56/9.45  tff(c_1688, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1261])).
% 16.56/9.45  tff(c_29745, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1688])).
% 16.56/9.45  tff(c_29748, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_29745])).
% 16.56/9.45  tff(c_29751, plain, (~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_6, c_29748])).
% 16.56/9.45  tff(c_29755, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_29751])).
% 16.56/9.45  tff(c_29758, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2965, c_29755])).
% 16.56/9.45  tff(c_29774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_29758])).
% 16.56/9.45  tff(c_29775, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_1688])).
% 16.56/9.45  tff(c_31941, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1') | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_31935, c_29775])).
% 16.56/9.45  tff(c_31979, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_340, c_31941])).
% 16.56/9.45  tff(c_31996, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2965, c_31979])).
% 16.56/9.45  tff(c_32012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_31996])).
% 16.56/9.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/9.45  
% 16.56/9.45  Inference rules
% 16.56/9.45  ----------------------
% 16.56/9.45  #Ref     : 0
% 16.56/9.45  #Sup     : 8818
% 16.56/9.45  #Fact    : 0
% 16.56/9.45  #Define  : 0
% 16.56/9.45  #Split   : 51
% 16.56/9.45  #Chain   : 0
% 16.56/9.45  #Close   : 0
% 16.56/9.45  
% 16.56/9.45  Ordering : KBO
% 16.56/9.45  
% 16.56/9.45  Simplification rules
% 16.56/9.45  ----------------------
% 16.56/9.45  #Subsume      : 3360
% 16.56/9.45  #Demod        : 503
% 16.56/9.45  #Tautology    : 212
% 16.56/9.45  #SimpNegUnit  : 60
% 16.56/9.45  #BackRed      : 24
% 16.56/9.45  
% 16.56/9.45  #Partial instantiations: 0
% 16.56/9.45  #Strategies tried      : 1
% 16.56/9.45  
% 16.56/9.45  Timing (in seconds)
% 16.56/9.45  ----------------------
% 16.56/9.45  Preprocessing        : 0.28
% 16.56/9.45  Parsing              : 0.15
% 16.56/9.45  CNF conversion       : 0.02
% 16.56/9.45  Main loop            : 8.26
% 16.56/9.45  Inferencing          : 1.04
% 16.56/9.45  Reduction            : 2.23
% 16.56/9.45  Demodulation         : 1.42
% 16.56/9.45  BG Simplification    : 0.12
% 16.56/9.45  Subsumption          : 4.37
% 16.56/9.45  Abstraction          : 0.17
% 16.56/9.45  MUC search           : 0.00
% 16.56/9.46  Cooper               : 0.00
% 16.56/9.46  Total                : 8.57
% 16.56/9.46  Index Insertion      : 0.00
% 16.56/9.46  Index Deletion       : 0.00
% 16.56/9.46  Index Matching       : 0.00
% 16.56/9.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
