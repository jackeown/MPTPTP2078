%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:40 EST 2020

% Result     : Theorem 43.22s
% Output     : CNFRefutation 43.51s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 166 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 358 expanded)
%              Number of equality atoms :   13 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_41,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_34])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(k2_xboole_0(A_43,C_44),B_45)
      | ~ r1_tarski(C_44,B_45)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_80,plain,(
    ! [B_45,C_44] :
      ( k2_xboole_0(B_45,C_44) = B_45
      | ~ r1_tarski(C_44,B_45)
      | ~ r1_tarski(B_45,B_45) ) ),
    inference(resolution,[status(thm)],[c_76,c_59])).

tff(c_87,plain,(
    ! [B_46,C_47] :
      ( k2_xboole_0(B_46,C_47) = B_46
      | ~ r1_tarski(C_47,B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_111,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_591,plain,(
    ! [C_73,B_74,A_75] :
      ( k2_xboole_0(k2_xboole_0(C_73,B_74),A_75) = k2_xboole_0(C_73,B_74)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_675,plain,(
    ! [A_76,C_77,B_78,A_79] :
      ( r1_tarski(A_76,k2_xboole_0(C_77,B_78))
      | ~ r1_tarski(A_76,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_8])).

tff(c_1268,plain,(
    ! [A_104,C_105,B_106,B_107] :
      ( r1_tarski(A_104,k2_xboole_0(C_105,B_106))
      | ~ r1_tarski(k2_xboole_0(A_104,B_107),B_106) ) ),
    inference(resolution,[status(thm)],[c_10,c_675])).

tff(c_1310,plain,(
    ! [A_108,C_109,B_110] : r1_tarski(A_108,k2_xboole_0(C_109,k2_xboole_0(A_108,B_110))) ),
    inference(resolution,[status(thm)],[c_6,c_1268])).

tff(c_1376,plain,(
    ! [B_2,C_109] : r1_tarski(B_2,k2_xboole_0(C_109,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_1310])).

tff(c_22,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k1_tops_1(A_18,B_22),k1_tops_1(A_18,C_24))
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_578,plain,(
    ! [A_70,B_71,C_72] :
      ( k4_subset_1(A_70,B_71,C_72) = k2_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4587,plain,(
    ! [A_173,B_174,B_175] :
      ( k4_subset_1(u1_struct_0(A_173),B_174,k1_tops_1(A_173,B_175)) = k2_xboole_0(B_174,k1_tops_1(A_173,B_175))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(resolution,[status(thm)],[c_20,c_578])).

tff(c_16580,plain,(
    ! [A_374,B_375,B_376] :
      ( k4_subset_1(u1_struct_0(A_374),k1_tops_1(A_374,B_375),k1_tops_1(A_374,B_376)) = k2_xboole_0(k1_tops_1(A_374,B_375),k1_tops_1(A_374,B_376))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ l1_pre_topc(A_374) ) ),
    inference(resolution,[status(thm)],[c_20,c_4587])).

tff(c_1030,plain,(
    ! [B_95] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_95,'#skF_3') = k2_xboole_0(B_95,'#skF_3')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_578])).

tff(c_1051,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1030])).

tff(c_24,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1092,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_24])).

tff(c_16594,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16580,c_1092])).

tff(c_16614,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_16594])).

tff(c_20095,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12,c_16614])).

tff(c_157388,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_20095])).

tff(c_157394,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_157388])).

tff(c_157398,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_10,c_157394])).

tff(c_157402,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_157398])).

tff(c_157417,plain,
    ( ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_157402])).

tff(c_157427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_41,c_157417])).

tff(c_157428,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_20095])).

tff(c_157568,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_157428])).

tff(c_157572,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1376,c_157568])).

tff(c_157576,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_157572])).

tff(c_157591,plain,
    ( ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_157576])).

tff(c_157601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_41,c_157591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:50:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.22/34.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.22/34.07  
% 43.22/34.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.22/34.07  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 43.22/34.07  
% 43.22/34.07  %Foreground sorts:
% 43.22/34.07  
% 43.22/34.07  
% 43.22/34.07  %Background operators:
% 43.22/34.07  
% 43.22/34.07  
% 43.22/34.07  %Foreground operators:
% 43.22/34.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.22/34.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 43.22/34.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.22/34.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 43.22/34.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 43.22/34.07  tff('#skF_2', type, '#skF_2': $i).
% 43.22/34.07  tff('#skF_3', type, '#skF_3': $i).
% 43.22/34.07  tff('#skF_1', type, '#skF_1': $i).
% 43.22/34.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 43.22/34.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.22/34.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.22/34.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.22/34.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 43.22/34.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 43.22/34.07  
% 43.51/34.09  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k4_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)), k1_tops_1(A, k4_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tops_1)).
% 43.51/34.09  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 43.51/34.09  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 43.51/34.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 43.51/34.09  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 43.51/34.09  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 43.51/34.09  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 43.51/34.09  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 43.51/34.09  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 43.51/34.09  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.51/34.09  tff(c_34, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 43.51/34.09  tff(c_42, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_34])).
% 43.51/34.09  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.51/34.09  tff(c_41, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_34])).
% 43.51/34.09  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.51/34.09  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 43.51/34.09  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.51/34.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.51/34.09  tff(c_76, plain, (![A_43, C_44, B_45]: (r1_tarski(k2_xboole_0(A_43, C_44), B_45) | ~r1_tarski(C_44, B_45) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.51/34.09  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 43.51/34.09  tff(c_48, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.51/34.09  tff(c_59, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(k2_xboole_0(A_6, B_7), A_6))), inference(resolution, [status(thm)], [c_10, c_48])).
% 43.51/34.09  tff(c_80, plain, (![B_45, C_44]: (k2_xboole_0(B_45, C_44)=B_45 | ~r1_tarski(C_44, B_45) | ~r1_tarski(B_45, B_45))), inference(resolution, [status(thm)], [c_76, c_59])).
% 43.51/34.09  tff(c_87, plain, (![B_46, C_47]: (k2_xboole_0(B_46, C_47)=B_46 | ~r1_tarski(C_47, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80])).
% 43.51/34.09  tff(c_111, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_87])).
% 43.51/34.09  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 43.51/34.09  tff(c_591, plain, (![C_73, B_74, A_75]: (k2_xboole_0(k2_xboole_0(C_73, B_74), A_75)=k2_xboole_0(C_73, B_74) | ~r1_tarski(A_75, B_74))), inference(resolution, [status(thm)], [c_8, c_87])).
% 43.51/34.09  tff(c_675, plain, (![A_76, C_77, B_78, A_79]: (r1_tarski(A_76, k2_xboole_0(C_77, B_78)) | ~r1_tarski(A_76, A_79) | ~r1_tarski(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_591, c_8])).
% 43.51/34.09  tff(c_1268, plain, (![A_104, C_105, B_106, B_107]: (r1_tarski(A_104, k2_xboole_0(C_105, B_106)) | ~r1_tarski(k2_xboole_0(A_104, B_107), B_106))), inference(resolution, [status(thm)], [c_10, c_675])).
% 43.51/34.09  tff(c_1310, plain, (![A_108, C_109, B_110]: (r1_tarski(A_108, k2_xboole_0(C_109, k2_xboole_0(A_108, B_110))))), inference(resolution, [status(thm)], [c_6, c_1268])).
% 43.51/34.09  tff(c_1376, plain, (![B_2, C_109]: (r1_tarski(B_2, k2_xboole_0(C_109, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_1310])).
% 43.51/34.09  tff(c_22, plain, (![A_18, B_22, C_24]: (r1_tarski(k1_tops_1(A_18, B_22), k1_tops_1(A_18, C_24)) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 43.51/34.09  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 43.51/34.09  tff(c_578, plain, (![A_70, B_71, C_72]: (k4_subset_1(A_70, B_71, C_72)=k2_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 43.51/34.09  tff(c_4587, plain, (![A_173, B_174, B_175]: (k4_subset_1(u1_struct_0(A_173), B_174, k1_tops_1(A_173, B_175))=k2_xboole_0(B_174, k1_tops_1(A_173, B_175)) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(resolution, [status(thm)], [c_20, c_578])).
% 43.51/34.09  tff(c_16580, plain, (![A_374, B_375, B_376]: (k4_subset_1(u1_struct_0(A_374), k1_tops_1(A_374, B_375), k1_tops_1(A_374, B_376))=k2_xboole_0(k1_tops_1(A_374, B_375), k1_tops_1(A_374, B_376)) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_374))) | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0(A_374))) | ~l1_pre_topc(A_374))), inference(resolution, [status(thm)], [c_20, c_4587])).
% 43.51/34.09  tff(c_1030, plain, (![B_95]: (k4_subset_1(u1_struct_0('#skF_1'), B_95, '#skF_3')=k2_xboole_0(B_95, '#skF_3') | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_578])).
% 43.51/34.09  tff(c_1051, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1030])).
% 43.51/34.09  tff(c_24, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.51/34.09  tff(c_1092, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_24])).
% 43.51/34.09  tff(c_16594, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16580, c_1092])).
% 43.51/34.09  tff(c_16614, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_16594])).
% 43.51/34.09  tff(c_20095, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_12, c_16614])).
% 43.51/34.09  tff(c_157388, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_20095])).
% 43.51/34.09  tff(c_157394, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_157388])).
% 43.51/34.09  tff(c_157398, plain, (~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_10, c_157394])).
% 43.51/34.09  tff(c_157402, plain, (~r1_tarski(k2_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_157398])).
% 43.51/34.09  tff(c_157417, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_157402])).
% 43.51/34.09  tff(c_157427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_41, c_157417])).
% 43.51/34.09  tff(c_157428, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_20095])).
% 43.51/34.09  tff(c_157568, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_157428])).
% 43.51/34.09  tff(c_157572, plain, (~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1376, c_157568])).
% 43.51/34.09  tff(c_157576, plain, (~r1_tarski(k2_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_157572])).
% 43.51/34.09  tff(c_157591, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_157576])).
% 43.51/34.09  tff(c_157601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_41, c_157591])).
% 43.51/34.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.51/34.09  
% 43.51/34.09  Inference rules
% 43.51/34.09  ----------------------
% 43.51/34.09  #Ref     : 0
% 43.51/34.09  #Sup     : 40203
% 43.51/34.09  #Fact    : 0
% 43.51/34.09  #Define  : 0
% 43.51/34.09  #Split   : 7
% 43.51/34.09  #Chain   : 0
% 43.51/34.09  #Close   : 0
% 43.51/34.09  
% 43.51/34.09  Ordering : KBO
% 43.51/34.09  
% 43.51/34.09  Simplification rules
% 43.51/34.09  ----------------------
% 43.51/34.09  #Subsume      : 8996
% 43.51/34.09  #Demod        : 20120
% 43.51/34.09  #Tautology    : 13487
% 43.51/34.09  #SimpNegUnit  : 4
% 43.51/34.09  #BackRed      : 1
% 43.51/34.09  
% 43.51/34.09  #Partial instantiations: 0
% 43.51/34.09  #Strategies tried      : 1
% 43.51/34.09  
% 43.51/34.09  Timing (in seconds)
% 43.51/34.09  ----------------------
% 43.51/34.09  Preprocessing        : 0.29
% 43.51/34.09  Parsing              : 0.15
% 43.51/34.09  CNF conversion       : 0.02
% 43.51/34.09  Main loop            : 33.06
% 43.51/34.09  Inferencing          : 2.89
% 43.51/34.09  Reduction            : 16.45
% 43.51/34.09  Demodulation         : 14.86
% 43.51/34.09  BG Simplification    : 0.43
% 43.51/34.09  Subsumption          : 11.99
% 43.51/34.09  Abstraction          : 0.75
% 43.51/34.09  MUC search           : 0.00
% 43.51/34.09  Cooper               : 0.00
% 43.51/34.09  Total                : 33.38
% 43.51/34.09  Index Insertion      : 0.00
% 43.51/34.09  Index Deletion       : 0.00
% 43.51/34.09  Index Matching       : 0.00
% 43.51/34.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
