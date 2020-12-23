%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:28 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 258 expanded)
%              Number of leaves         :   35 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 671 expanded)
%              Number of equality atoms :    8 (  81 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_30,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_17] :
      ( v4_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_47,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_83,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_47,c_83])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_110,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(u1_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_113,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_110])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_113])).

tff(c_115,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_118,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_118])).

tff(c_123,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_77,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_32])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [C_53,A_54,B_55] :
      ( r2_hidden(C_53,A_54)
      | ~ r2_hidden(C_53,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_212,plain,(
    ! [A_60,A_61,B_62] :
      ( r2_hidden(A_60,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61))
      | v1_xboole_0(B_62)
      | ~ m1_subset_1(A_60,B_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_157])).

tff(c_237,plain,(
    ! [A_64,B_65,A_66] :
      ( r2_hidden(A_64,B_65)
      | v1_xboole_0(A_66)
      | ~ m1_subset_1(A_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_243,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_2',B_65)
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ r1_tarski(k2_struct_0('#skF_1'),B_65) ) ),
    inference(resolution,[status(thm)],[c_77,c_237])).

tff(c_253,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_2',B_67)
      | ~ r1_tarski(k2_struct_0('#skF_1'),B_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_243])).

tff(c_258,plain,(
    r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_96,c_253])).

tff(c_46,plain,(
    ! [D_30] :
      ( v3_pre_topc(D_30,'#skF_1')
      | ~ r2_hidden(D_30,'#skF_3')
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_99,plain,(
    ! [D_44] :
      ( v3_pre_topc(D_44,'#skF_1')
      | ~ r2_hidden(D_44,'#skF_3')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_46])).

tff(c_109,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_99])).

tff(c_138,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_40,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_3')
      | ~ r2_hidden('#skF_2',D_30)
      | ~ v4_pre_topc(D_30,'#skF_1')
      | ~ v3_pre_topc(D_30,'#skF_1')
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_223,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_3')
      | ~ r2_hidden('#skF_2',D_63)
      | ~ v4_pre_topc(D_63,'#skF_1')
      | ~ v3_pre_topc(D_63,'#skF_1')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40])).

tff(c_231,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_223])).

tff(c_235,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_231])).

tff(c_281,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_235])).

tff(c_282,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_285,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_282])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_285])).

tff(c_290,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_294,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_290])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_294])).

tff(c_300,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_316,plain,(
    ! [C_74,A_75,B_76] :
      ( r2_hidden(C_74,A_75)
      | ~ r2_hidden(C_74,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_373,plain,(
    ! [A_81] :
      ( r2_hidden(k2_struct_0('#skF_1'),A_81)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_300,c_316])).

tff(c_4,plain,(
    ! [A_2,B_3] : ~ r2_hidden(A_2,k2_zfmisc_1(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_382,plain,(
    ! [B_82] : ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),B_82))) ),
    inference(resolution,[status(thm)],[c_373,c_4])).

tff(c_385,plain,(
    ! [B_82] : ~ r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),B_82)) ),
    inference(resolution,[status(thm)],[c_16,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:51:14 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.44  
% 2.36/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.45  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.45  
% 2.36/1.45  %Foreground sorts:
% 2.36/1.45  
% 2.36/1.45  
% 2.36/1.45  %Background operators:
% 2.36/1.45  
% 2.36/1.45  
% 2.36/1.45  %Foreground operators:
% 2.36/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.36/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.36/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.36/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.36/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.36/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.36/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.36/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.45  
% 2.74/1.46  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.74/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.74/1.46  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.46  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.74/1.46  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.74/1.46  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.74/1.46  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.74/1.46  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.74/1.46  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.74/1.46  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.74/1.46  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.74/1.46  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.74/1.46  tff(f_30, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.74/1.46  tff(c_28, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.46  tff(c_48, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2])).
% 2.74/1.46  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.74/1.46  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_24, plain, (![A_17]: (v4_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.74/1.46  tff(c_26, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.46  tff(c_6, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.46  tff(c_8, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.74/1.46  tff(c_47, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.74/1.46  tff(c_83, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.74/1.46  tff(c_96, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_47, c_83])).
% 2.74/1.46  tff(c_20, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.74/1.46  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_66, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.46  tff(c_71, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_20, c_66])).
% 2.74/1.46  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.74/1.46  tff(c_110, plain, (![A_45]: (~v1_xboole_0(u1_struct_0(A_45)) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.74/1.46  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_110])).
% 2.74/1.46  tff(c_114, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_113])).
% 2.74/1.46  tff(c_115, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 2.74/1.46  tff(c_118, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_115])).
% 2.74/1.46  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_118])).
% 2.74/1.46  tff(c_123, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_114])).
% 2.74/1.46  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_77, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_32])).
% 2.74/1.46  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.46  tff(c_157, plain, (![C_53, A_54, B_55]: (r2_hidden(C_53, A_54) | ~r2_hidden(C_53, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.46  tff(c_212, plain, (![A_60, A_61, B_62]: (r2_hidden(A_60, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)) | v1_xboole_0(B_62) | ~m1_subset_1(A_60, B_62))), inference(resolution, [status(thm)], [c_12, c_157])).
% 2.74/1.46  tff(c_237, plain, (![A_64, B_65, A_66]: (r2_hidden(A_64, B_65) | v1_xboole_0(A_66) | ~m1_subset_1(A_64, A_66) | ~r1_tarski(A_66, B_65))), inference(resolution, [status(thm)], [c_16, c_212])).
% 2.74/1.46  tff(c_243, plain, (![B_65]: (r2_hidden('#skF_2', B_65) | v1_xboole_0(k2_struct_0('#skF_1')) | ~r1_tarski(k2_struct_0('#skF_1'), B_65))), inference(resolution, [status(thm)], [c_77, c_237])).
% 2.74/1.46  tff(c_253, plain, (![B_67]: (r2_hidden('#skF_2', B_67) | ~r1_tarski(k2_struct_0('#skF_1'), B_67))), inference(negUnitSimplification, [status(thm)], [c_123, c_243])).
% 2.74/1.46  tff(c_258, plain, (r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_96, c_253])).
% 2.74/1.46  tff(c_46, plain, (![D_30]: (v3_pre_topc(D_30, '#skF_1') | ~r2_hidden(D_30, '#skF_3') | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_99, plain, (![D_44]: (v3_pre_topc(D_44, '#skF_1') | ~r2_hidden(D_44, '#skF_3') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_46])).
% 2.74/1.46  tff(c_109, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_47, c_99])).
% 2.74/1.46  tff(c_138, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_109])).
% 2.74/1.46  tff(c_40, plain, (![D_30]: (r2_hidden(D_30, '#skF_3') | ~r2_hidden('#skF_2', D_30) | ~v4_pre_topc(D_30, '#skF_1') | ~v3_pre_topc(D_30, '#skF_1') | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.46  tff(c_223, plain, (![D_63]: (r2_hidden(D_63, '#skF_3') | ~r2_hidden('#skF_2', D_63) | ~v4_pre_topc(D_63, '#skF_1') | ~v3_pre_topc(D_63, '#skF_1') | ~m1_subset_1(D_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_40])).
% 2.74/1.46  tff(c_231, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_47, c_223])).
% 2.74/1.46  tff(c_235, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_138, c_231])).
% 2.74/1.46  tff(c_281, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_235])).
% 2.74/1.46  tff(c_282, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_281])).
% 2.74/1.46  tff(c_285, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_282])).
% 2.74/1.46  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_285])).
% 2.74/1.46  tff(c_290, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_281])).
% 2.74/1.46  tff(c_294, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_290])).
% 2.74/1.46  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_294])).
% 2.74/1.46  tff(c_300, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_109])).
% 2.74/1.46  tff(c_316, plain, (![C_74, A_75, B_76]: (r2_hidden(C_74, A_75) | ~r2_hidden(C_74, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.46  tff(c_373, plain, (![A_81]: (r2_hidden(k2_struct_0('#skF_1'), A_81) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_300, c_316])).
% 2.74/1.46  tff(c_4, plain, (![A_2, B_3]: (~r2_hidden(A_2, k2_zfmisc_1(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.74/1.46  tff(c_382, plain, (![B_82]: (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), B_82))))), inference(resolution, [status(thm)], [c_373, c_4])).
% 2.74/1.46  tff(c_385, plain, (![B_82]: (~r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), B_82)))), inference(resolution, [status(thm)], [c_16, c_382])).
% 2.74/1.46  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_385])).
% 2.74/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.46  
% 2.74/1.46  Inference rules
% 2.74/1.46  ----------------------
% 2.74/1.46  #Ref     : 0
% 2.74/1.46  #Sup     : 61
% 2.74/1.46  #Fact    : 0
% 2.74/1.46  #Define  : 0
% 2.74/1.46  #Split   : 8
% 2.74/1.46  #Chain   : 0
% 2.74/1.46  #Close   : 0
% 2.74/1.46  
% 2.74/1.46  Ordering : KBO
% 2.74/1.46  
% 2.74/1.46  Simplification rules
% 2.74/1.46  ----------------------
% 2.74/1.46  #Subsume      : 9
% 2.74/1.46  #Demod        : 29
% 2.74/1.46  #Tautology    : 13
% 2.74/1.46  #SimpNegUnit  : 3
% 2.74/1.46  #BackRed      : 2
% 2.74/1.46  
% 2.74/1.46  #Partial instantiations: 0
% 2.74/1.46  #Strategies tried      : 1
% 2.74/1.46  
% 2.74/1.46  Timing (in seconds)
% 2.74/1.46  ----------------------
% 2.74/1.47  Preprocessing        : 0.36
% 2.74/1.47  Parsing              : 0.18
% 2.74/1.47  CNF conversion       : 0.03
% 2.74/1.47  Main loop            : 0.26
% 2.74/1.47  Inferencing          : 0.09
% 2.74/1.47  Reduction            : 0.08
% 2.74/1.47  Demodulation         : 0.05
% 2.74/1.47  BG Simplification    : 0.02
% 2.74/1.47  Subsumption          : 0.05
% 2.74/1.47  Abstraction          : 0.01
% 2.74/1.47  MUC search           : 0.00
% 2.74/1.47  Cooper               : 0.00
% 2.74/1.47  Total                : 0.65
% 2.74/1.47  Index Insertion      : 0.00
% 2.74/1.47  Index Deletion       : 0.00
% 2.74/1.47  Index Matching       : 0.00
% 2.74/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
