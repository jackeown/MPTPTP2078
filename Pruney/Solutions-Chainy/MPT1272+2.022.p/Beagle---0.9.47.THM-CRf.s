%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:01 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 163 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  138 ( 401 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,k2_tops_1(A_35,B_34))
      | ~ v2_tops_1(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_64,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_60])).

tff(c_65,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_30,plain,(
    ! [B_25,A_26] :
      ( r1_tarski(B_25,k2_pre_topc(A_26,B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_35,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_67,plain,(
    ! [A_38,B_39] :
      ( v2_tops_1(k2_pre_topc(A_38,B_39),A_38)
      | ~ v3_tops_1(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_75,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_71])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_pre_topc(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( r1_tarski(B_8,k2_pre_topc(A_6,B_8))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k2_pre_topc(A_30,B_31),k2_pre_topc(A_30,k2_pre_topc(A_30,B_31)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_51,c_6])).

tff(c_107,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k2_pre_topc(A_48,B_49),k2_pre_topc(A_48,k2_pre_topc(A_48,B_49)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_51,c_6])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_55,A_56,B_57] :
      ( r1_tarski(A_55,k2_pre_topc(A_56,k2_pre_topc(A_56,B_57)))
      | ~ r1_tarski(A_55,k2_pre_topc(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_158,plain,(
    ! [A_64,A_65,B_66,A_67] :
      ( r1_tarski(A_64,k2_pre_topc(A_65,k2_pre_topc(A_65,B_66)))
      | ~ r1_tarski(A_64,A_67)
      | ~ r1_tarski(A_67,k2_pre_topc(A_65,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_183,plain,(
    ! [A_68,B_69] :
      ( r1_tarski('#skF_2',k2_pre_topc(A_68,k2_pre_topc(A_68,B_69)))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc(A_68,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_35,c_158])).

tff(c_189,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_183])).

tff(c_196,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_189])).

tff(c_201,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_204,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_204])).

tff(c_210,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_20,plain,(
    ! [B_20,A_18] :
      ( r1_tarski(B_20,k2_tops_1(A_18,B_20))
      | ~ v2_tops_1(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_214,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_210,c_20])).

tff(c_222,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75,c_214])).

tff(c_81,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k2_tops_1(A_40,k2_pre_topc(A_40,B_41)),k2_tops_1(A_40,B_41))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    ! [A_1,A_40,B_41] :
      ( r1_tarski(A_1,k2_tops_1(A_40,B_41))
      | ~ r1_tarski(A_1,k2_tops_1(A_40,k2_pre_topc(A_40,B_41)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_272,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_222,c_87])).

tff(c_282,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_272])).

tff(c_319,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_76,k2_pre_topc('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_282,c_2])).

tff(c_18,plain,(
    ! [B_20,A_18] :
      ( v2_tops_1(B_20,A_18)
      | ~ r1_tarski(B_20,k2_tops_1(A_18,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_324,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_319,c_18])).

tff(c_332,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_28,c_26,c_324])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_332])).

tff(c_336,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_392,plain,(
    ! [A_84,B_85] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_84),B_85),A_84)
      | ~ v2_tops_1(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_395,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_392,c_22])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_336,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  
% 2.67/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.67/1.38  
% 2.67/1.38  %Foreground sorts:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Background operators:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Foreground operators:
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.38  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.67/1.38  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.67/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.38  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.67/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.67/1.38  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.67/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.67/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.38  
% 2.67/1.40  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 2.67/1.40  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 2.67/1.40  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.67/1.40  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 2.67/1.40  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.67/1.40  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.67/1.40  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 2.67/1.40  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 2.67/1.40  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.40  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.40  tff(c_56, plain, (![B_34, A_35]: (r1_tarski(B_34, k2_tops_1(A_35, B_34)) | ~v2_tops_1(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.40  tff(c_60, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.67/1.40  tff(c_64, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_60])).
% 2.67/1.40  tff(c_65, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 2.67/1.40  tff(c_30, plain, (![B_25, A_26]: (r1_tarski(B_25, k2_pre_topc(A_26, B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.40  tff(c_32, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.67/1.40  tff(c_35, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.67/1.40  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.40  tff(c_67, plain, (![A_38, B_39]: (v2_tops_1(k2_pre_topc(A_38, B_39), A_38) | ~v3_tops_1(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.40  tff(c_71, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.67/1.40  tff(c_75, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_71])).
% 2.67/1.40  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k2_pre_topc(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.40  tff(c_51, plain, (![A_30, B_31]: (m1_subset_1(k2_pre_topc(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.40  tff(c_6, plain, (![B_8, A_6]: (r1_tarski(B_8, k2_pre_topc(A_6, B_8)) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.40  tff(c_54, plain, (![A_30, B_31]: (r1_tarski(k2_pre_topc(A_30, B_31), k2_pre_topc(A_30, k2_pre_topc(A_30, B_31))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_51, c_6])).
% 2.67/1.40  tff(c_107, plain, (![A_48, B_49]: (r1_tarski(k2_pre_topc(A_48, B_49), k2_pre_topc(A_48, k2_pre_topc(A_48, B_49))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_51, c_6])).
% 2.67/1.40  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.40  tff(c_124, plain, (![A_55, A_56, B_57]: (r1_tarski(A_55, k2_pre_topc(A_56, k2_pre_topc(A_56, B_57))) | ~r1_tarski(A_55, k2_pre_topc(A_56, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.67/1.40  tff(c_158, plain, (![A_64, A_65, B_66, A_67]: (r1_tarski(A_64, k2_pre_topc(A_65, k2_pre_topc(A_65, B_66))) | ~r1_tarski(A_64, A_67) | ~r1_tarski(A_67, k2_pre_topc(A_65, B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_124, c_2])).
% 2.67/1.40  tff(c_183, plain, (![A_68, B_69]: (r1_tarski('#skF_2', k2_pre_topc(A_68, k2_pre_topc(A_68, B_69))) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc(A_68, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_35, c_158])).
% 2.67/1.40  tff(c_189, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_183])).
% 2.67/1.40  tff(c_196, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_189])).
% 2.67/1.40  tff(c_201, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_196])).
% 2.67/1.40  tff(c_204, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_201])).
% 2.67/1.40  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_204])).
% 2.67/1.40  tff(c_210, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_196])).
% 2.67/1.40  tff(c_20, plain, (![B_20, A_18]: (r1_tarski(B_20, k2_tops_1(A_18, B_20)) | ~v2_tops_1(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.40  tff(c_214, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_210, c_20])).
% 2.67/1.40  tff(c_222, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75, c_214])).
% 2.67/1.40  tff(c_81, plain, (![A_40, B_41]: (r1_tarski(k2_tops_1(A_40, k2_pre_topc(A_40, B_41)), k2_tops_1(A_40, B_41)) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.40  tff(c_87, plain, (![A_1, A_40, B_41]: (r1_tarski(A_1, k2_tops_1(A_40, B_41)) | ~r1_tarski(A_1, k2_tops_1(A_40, k2_pre_topc(A_40, B_41))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.67/1.40  tff(c_272, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_222, c_87])).
% 2.67/1.40  tff(c_282, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_272])).
% 2.67/1.40  tff(c_319, plain, (![A_76]: (r1_tarski(A_76, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_76, k2_pre_topc('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_282, c_2])).
% 2.67/1.40  tff(c_18, plain, (![B_20, A_18]: (v2_tops_1(B_20, A_18) | ~r1_tarski(B_20, k2_tops_1(A_18, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.40  tff(c_324, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_319, c_18])).
% 2.67/1.40  tff(c_332, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_28, c_26, c_324])).
% 2.67/1.40  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_332])).
% 2.67/1.40  tff(c_336, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 2.67/1.40  tff(c_392, plain, (![A_84, B_85]: (v1_tops_1(k3_subset_1(u1_struct_0(A_84), B_85), A_84) | ~v2_tops_1(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.40  tff(c_22, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.40  tff(c_395, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_392, c_22])).
% 2.67/1.40  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_336, c_395])).
% 2.67/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  Inference rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Ref     : 0
% 2.67/1.40  #Sup     : 87
% 2.67/1.40  #Fact    : 0
% 2.67/1.40  #Define  : 0
% 2.67/1.40  #Split   : 3
% 2.67/1.40  #Chain   : 0
% 2.67/1.40  #Close   : 0
% 2.67/1.40  
% 2.67/1.40  Ordering : KBO
% 2.67/1.40  
% 2.67/1.40  Simplification rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Subsume      : 7
% 2.67/1.40  #Demod        : 56
% 2.67/1.40  #Tautology    : 15
% 2.67/1.40  #SimpNegUnit  : 1
% 2.67/1.40  #BackRed      : 0
% 2.67/1.40  
% 2.67/1.40  #Partial instantiations: 0
% 2.67/1.40  #Strategies tried      : 1
% 2.67/1.40  
% 2.67/1.40  Timing (in seconds)
% 2.67/1.40  ----------------------
% 2.67/1.40  Preprocessing        : 0.31
% 2.67/1.40  Parsing              : 0.18
% 2.67/1.40  CNF conversion       : 0.02
% 2.67/1.40  Main loop            : 0.28
% 2.67/1.40  Inferencing          : 0.11
% 2.67/1.40  Reduction            : 0.07
% 2.67/1.40  Demodulation         : 0.05
% 2.67/1.40  BG Simplification    : 0.02
% 2.67/1.40  Subsumption          : 0.07
% 2.67/1.40  Abstraction          : 0.01
% 2.67/1.40  MUC search           : 0.00
% 2.67/1.40  Cooper               : 0.00
% 2.67/1.40  Total                : 0.63
% 2.67/1.40  Index Insertion      : 0.00
% 2.67/1.40  Index Deletion       : 0.00
% 2.67/1.40  Index Matching       : 0.00
% 2.67/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
