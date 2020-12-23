%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 150 expanded)
%              Number of leaves         :   37 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 311 expanded)
%              Number of equality atoms :   20 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_70,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_50,plain,(
    k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    ! [A_32] :
      ( v1_xboole_0(k1_struct_0(A_32))
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_108,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_2'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_59,B_60] :
      ( ~ v1_xboole_0(A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_22,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_3'(A_63,B_64),B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,(
    ! [B_64,A_63] :
      ( ~ v1_xboole_0(B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_26,plain,(
    ! [A_20] : k2_subset_1(A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_21] : m1_subset_1(k2_subset_1(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [A_21] : m1_subset_1(A_21,k1_zfmisc_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [A_33] :
      ( k3_subset_1(u1_struct_0(A_33),k1_struct_0(A_33)) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_383,plain,(
    ! [B_125,A_126,C_127] :
      ( r1_tarski(B_125,k3_subset_1(A_126,C_127))
      | ~ r1_xboole_0(B_125,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1542,plain,(
    ! [B_259,A_260] :
      ( r1_tarski(B_259,k2_struct_0(A_260))
      | ~ r1_xboole_0(B_259,k1_struct_0(A_260))
      | ~ m1_subset_1(k1_struct_0(A_260),k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_struct_0(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_383])).

tff(c_3442,plain,(
    ! [B_425,A_426] :
      ( r1_tarski(B_425,k2_struct_0(A_426))
      | ~ r1_xboole_0(B_425,k1_struct_0(A_426))
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_struct_0(A_426)
      | ~ r1_tarski(k1_struct_0(A_426),u1_struct_0(A_426)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1542])).

tff(c_4110,plain,(
    ! [A_501] :
      ( r1_tarski(u1_struct_0(A_501),k2_struct_0(A_501))
      | ~ r1_xboole_0(u1_struct_0(A_501),k1_struct_0(A_501))
      | ~ l1_struct_0(A_501)
      | ~ r1_tarski(k1_struct_0(A_501),u1_struct_0(A_501)) ) ),
    inference(resolution,[status(thm)],[c_53,c_3442])).

tff(c_4200,plain,(
    ! [A_506] :
      ( r1_tarski(u1_struct_0(A_506),k2_struct_0(A_506))
      | ~ l1_struct_0(A_506)
      | ~ r1_tarski(k1_struct_0(A_506),u1_struct_0(A_506))
      | ~ v1_xboole_0(k1_struct_0(A_506)) ) ),
    inference(resolution,[status(thm)],[c_127,c_4110])).

tff(c_99,plain,(
    ! [A_57] :
      ( m1_subset_1(k2_struct_0(A_57),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_103,plain,(
    ! [A_57] :
      ( r1_tarski(k2_struct_0(A_57),u1_struct_0(A_57))
      | ~ l1_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_99,c_34])).

tff(c_198,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(A_87,C_88)
      | ~ r1_tarski(B_89,C_88)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_297,plain,(
    ! [A_106,A_107] :
      ( r1_tarski(A_106,u1_struct_0(A_107))
      | ~ r1_tarski(A_106,k2_struct_0(A_107))
      | ~ l1_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_103,c_198])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_314,plain,(
    ! [A_107,A_106] :
      ( u1_struct_0(A_107) = A_106
      | ~ r1_tarski(u1_struct_0(A_107),A_106)
      | ~ r1_tarski(A_106,k2_struct_0(A_107))
      | ~ l1_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_297,c_18])).

tff(c_4237,plain,(
    ! [A_506] :
      ( u1_struct_0(A_506) = k2_struct_0(A_506)
      | ~ r1_tarski(k2_struct_0(A_506),k2_struct_0(A_506))
      | ~ l1_struct_0(A_506)
      | ~ r1_tarski(k1_struct_0(A_506),u1_struct_0(A_506))
      | ~ v1_xboole_0(k1_struct_0(A_506)) ) ),
    inference(resolution,[status(thm)],[c_4200,c_314])).

tff(c_4312,plain,(
    ! [A_507] :
      ( u1_struct_0(A_507) = k2_struct_0(A_507)
      | ~ l1_struct_0(A_507)
      | ~ r1_tarski(k1_struct_0(A_507),u1_struct_0(A_507))
      | ~ v1_xboole_0(k1_struct_0(A_507)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4237])).

tff(c_4322,plain,(
    ! [A_508] :
      ( u1_struct_0(A_508) = k2_struct_0(A_508)
      | ~ l1_struct_0(A_508)
      | ~ v1_xboole_0(k1_struct_0(A_508)) ) ),
    inference(resolution,[status(thm)],[c_118,c_4312])).

tff(c_4327,plain,(
    ! [A_509] :
      ( u1_struct_0(A_509) = k2_struct_0(A_509)
      | ~ l1_struct_0(A_509) ) ),
    inference(resolution,[status(thm)],[c_44,c_4322])).

tff(c_4332,plain,(
    ! [A_510] :
      ( u1_struct_0(A_510) = k2_struct_0(A_510)
      | ~ l1_pre_topc(A_510) ) ),
    inference(resolution,[status(thm)],[c_42,c_4327])).

tff(c_4336,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4332])).

tff(c_288,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k2_pre_topc(A_103,B_104),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_295,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k2_pre_topc(A_103,B_104),u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_288,c_34])).

tff(c_239,plain,(
    ! [B_97,A_98] :
      ( r1_tarski(B_97,k2_pre_topc(A_98,B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_445,plain,(
    ! [A_136,A_137] :
      ( r1_tarski(A_136,k2_pre_topc(A_137,A_136))
      | ~ l1_pre_topc(A_137)
      | ~ r1_tarski(A_136,u1_struct_0(A_137)) ) ),
    inference(resolution,[status(thm)],[c_36,c_239])).

tff(c_1192,plain,(
    ! [A_231,A_232] :
      ( k2_pre_topc(A_231,A_232) = A_232
      | ~ r1_tarski(k2_pre_topc(A_231,A_232),A_232)
      | ~ l1_pre_topc(A_231)
      | ~ r1_tarski(A_232,u1_struct_0(A_231)) ) ),
    inference(resolution,[status(thm)],[c_445,c_18])).

tff(c_1204,plain,(
    ! [A_103] :
      ( k2_pre_topc(A_103,u1_struct_0(A_103)) = u1_struct_0(A_103)
      | ~ r1_tarski(u1_struct_0(A_103),u1_struct_0(A_103))
      | ~ m1_subset_1(u1_struct_0(A_103),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_295,c_1192])).

tff(c_1221,plain,(
    ! [A_103] :
      ( k2_pre_topc(A_103,u1_struct_0(A_103)) = u1_struct_0(A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_22,c_1204])).

tff(c_4442,plain,
    ( k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4336,c_1221])).

tff(c_4567,plain,(
    k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4336,c_4442])).

tff(c_4569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.43  
% 6.59/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 6.59/2.43  
% 6.59/2.43  %Foreground sorts:
% 6.59/2.43  
% 6.59/2.43  
% 6.59/2.43  %Background operators:
% 6.59/2.43  
% 6.59/2.43  
% 6.59/2.43  %Foreground operators:
% 6.59/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.59/2.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.59/2.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.59/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.59/2.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.59/2.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.59/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.59/2.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.59/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.43  tff('#skF_4', type, '#skF_4': $i).
% 6.59/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.59/2.43  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 6.59/2.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.59/2.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.59/2.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.59/2.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.59/2.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.59/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.59/2.43  
% 6.59/2.45  tff(f_119, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 6.59/2.45  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.59/2.45  tff(f_103, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 6.59/2.45  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.59/2.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.59/2.45  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.59/2.45  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.59/2.45  tff(f_70, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.59/2.45  tff(f_72, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.59/2.45  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.59/2.45  tff(f_107, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 6.59/2.45  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 6.59/2.45  tff(f_95, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 6.59/2.45  tff(f_68, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.59/2.45  tff(f_91, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.59/2.45  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 6.59/2.45  tff(c_50, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.59/2.45  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.59/2.45  tff(c_42, plain, (![A_31]: (l1_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.59/2.45  tff(c_44, plain, (![A_32]: (v1_xboole_0(k1_struct_0(A_32)) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.59/2.45  tff(c_108, plain, (![A_59, B_60]: (r2_hidden('#skF_2'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.59/2.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.45  tff(c_118, plain, (![A_59, B_60]: (~v1_xboole_0(A_59) | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_108, c_2])).
% 6.59/2.45  tff(c_22, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.59/2.45  tff(c_123, plain, (![A_63, B_64]: (r2_hidden('#skF_3'(A_63, B_64), B_64) | r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.59/2.45  tff(c_127, plain, (![B_64, A_63]: (~v1_xboole_0(B_64) | r1_xboole_0(A_63, B_64))), inference(resolution, [status(thm)], [c_123, c_2])).
% 6.59/2.45  tff(c_26, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.59/2.45  tff(c_28, plain, (![A_21]: (m1_subset_1(k2_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.59/2.45  tff(c_53, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 6.59/2.45  tff(c_36, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.59/2.45  tff(c_46, plain, (![A_33]: (k3_subset_1(u1_struct_0(A_33), k1_struct_0(A_33))=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.59/2.45  tff(c_383, plain, (![B_125, A_126, C_127]: (r1_tarski(B_125, k3_subset_1(A_126, C_127)) | ~r1_xboole_0(B_125, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_126)) | ~m1_subset_1(B_125, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.59/2.45  tff(c_1542, plain, (![B_259, A_260]: (r1_tarski(B_259, k2_struct_0(A_260)) | ~r1_xboole_0(B_259, k1_struct_0(A_260)) | ~m1_subset_1(k1_struct_0(A_260), k1_zfmisc_1(u1_struct_0(A_260))) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_struct_0(A_260))), inference(superposition, [status(thm), theory('equality')], [c_46, c_383])).
% 6.59/2.45  tff(c_3442, plain, (![B_425, A_426]: (r1_tarski(B_425, k2_struct_0(A_426)) | ~r1_xboole_0(B_425, k1_struct_0(A_426)) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_struct_0(A_426) | ~r1_tarski(k1_struct_0(A_426), u1_struct_0(A_426)))), inference(resolution, [status(thm)], [c_36, c_1542])).
% 6.59/2.45  tff(c_4110, plain, (![A_501]: (r1_tarski(u1_struct_0(A_501), k2_struct_0(A_501)) | ~r1_xboole_0(u1_struct_0(A_501), k1_struct_0(A_501)) | ~l1_struct_0(A_501) | ~r1_tarski(k1_struct_0(A_501), u1_struct_0(A_501)))), inference(resolution, [status(thm)], [c_53, c_3442])).
% 6.59/2.45  tff(c_4200, plain, (![A_506]: (r1_tarski(u1_struct_0(A_506), k2_struct_0(A_506)) | ~l1_struct_0(A_506) | ~r1_tarski(k1_struct_0(A_506), u1_struct_0(A_506)) | ~v1_xboole_0(k1_struct_0(A_506)))), inference(resolution, [status(thm)], [c_127, c_4110])).
% 6.59/2.45  tff(c_99, plain, (![A_57]: (m1_subset_1(k2_struct_0(A_57), k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.59/2.45  tff(c_34, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.59/2.45  tff(c_103, plain, (![A_57]: (r1_tarski(k2_struct_0(A_57), u1_struct_0(A_57)) | ~l1_struct_0(A_57))), inference(resolution, [status(thm)], [c_99, c_34])).
% 6.59/2.45  tff(c_198, plain, (![A_87, C_88, B_89]: (r1_tarski(A_87, C_88) | ~r1_tarski(B_89, C_88) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.59/2.45  tff(c_297, plain, (![A_106, A_107]: (r1_tarski(A_106, u1_struct_0(A_107)) | ~r1_tarski(A_106, k2_struct_0(A_107)) | ~l1_struct_0(A_107))), inference(resolution, [status(thm)], [c_103, c_198])).
% 6.59/2.45  tff(c_18, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.59/2.45  tff(c_314, plain, (![A_107, A_106]: (u1_struct_0(A_107)=A_106 | ~r1_tarski(u1_struct_0(A_107), A_106) | ~r1_tarski(A_106, k2_struct_0(A_107)) | ~l1_struct_0(A_107))), inference(resolution, [status(thm)], [c_297, c_18])).
% 6.59/2.45  tff(c_4237, plain, (![A_506]: (u1_struct_0(A_506)=k2_struct_0(A_506) | ~r1_tarski(k2_struct_0(A_506), k2_struct_0(A_506)) | ~l1_struct_0(A_506) | ~r1_tarski(k1_struct_0(A_506), u1_struct_0(A_506)) | ~v1_xboole_0(k1_struct_0(A_506)))), inference(resolution, [status(thm)], [c_4200, c_314])).
% 6.59/2.45  tff(c_4312, plain, (![A_507]: (u1_struct_0(A_507)=k2_struct_0(A_507) | ~l1_struct_0(A_507) | ~r1_tarski(k1_struct_0(A_507), u1_struct_0(A_507)) | ~v1_xboole_0(k1_struct_0(A_507)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4237])).
% 6.59/2.45  tff(c_4322, plain, (![A_508]: (u1_struct_0(A_508)=k2_struct_0(A_508) | ~l1_struct_0(A_508) | ~v1_xboole_0(k1_struct_0(A_508)))), inference(resolution, [status(thm)], [c_118, c_4312])).
% 6.59/2.45  tff(c_4327, plain, (![A_509]: (u1_struct_0(A_509)=k2_struct_0(A_509) | ~l1_struct_0(A_509))), inference(resolution, [status(thm)], [c_44, c_4322])).
% 6.59/2.45  tff(c_4332, plain, (![A_510]: (u1_struct_0(A_510)=k2_struct_0(A_510) | ~l1_pre_topc(A_510))), inference(resolution, [status(thm)], [c_42, c_4327])).
% 6.59/2.45  tff(c_4336, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_4332])).
% 6.59/2.45  tff(c_288, plain, (![A_103, B_104]: (m1_subset_1(k2_pre_topc(A_103, B_104), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.59/2.45  tff(c_295, plain, (![A_103, B_104]: (r1_tarski(k2_pre_topc(A_103, B_104), u1_struct_0(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_288, c_34])).
% 6.59/2.45  tff(c_239, plain, (![B_97, A_98]: (r1_tarski(B_97, k2_pre_topc(A_98, B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.59/2.45  tff(c_445, plain, (![A_136, A_137]: (r1_tarski(A_136, k2_pre_topc(A_137, A_136)) | ~l1_pre_topc(A_137) | ~r1_tarski(A_136, u1_struct_0(A_137)))), inference(resolution, [status(thm)], [c_36, c_239])).
% 6.59/2.45  tff(c_1192, plain, (![A_231, A_232]: (k2_pre_topc(A_231, A_232)=A_232 | ~r1_tarski(k2_pre_topc(A_231, A_232), A_232) | ~l1_pre_topc(A_231) | ~r1_tarski(A_232, u1_struct_0(A_231)))), inference(resolution, [status(thm)], [c_445, c_18])).
% 6.59/2.45  tff(c_1204, plain, (![A_103]: (k2_pre_topc(A_103, u1_struct_0(A_103))=u1_struct_0(A_103) | ~r1_tarski(u1_struct_0(A_103), u1_struct_0(A_103)) | ~m1_subset_1(u1_struct_0(A_103), k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_295, c_1192])).
% 6.59/2.45  tff(c_1221, plain, (![A_103]: (k2_pre_topc(A_103, u1_struct_0(A_103))=u1_struct_0(A_103) | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_22, c_1204])).
% 6.59/2.45  tff(c_4442, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4336, c_1221])).
% 6.59/2.45  tff(c_4567, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4336, c_4442])).
% 6.59/2.45  tff(c_4569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_4567])).
% 6.59/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.45  
% 6.59/2.45  Inference rules
% 6.59/2.45  ----------------------
% 6.59/2.45  #Ref     : 0
% 6.59/2.45  #Sup     : 1184
% 6.59/2.45  #Fact    : 0
% 6.59/2.45  #Define  : 0
% 6.59/2.45  #Split   : 2
% 6.59/2.45  #Chain   : 0
% 6.59/2.45  #Close   : 0
% 6.59/2.45  
% 6.59/2.45  Ordering : KBO
% 6.59/2.45  
% 6.59/2.45  Simplification rules
% 6.59/2.45  ----------------------
% 6.59/2.45  #Subsume      : 579
% 6.59/2.45  #Demod        : 142
% 6.59/2.45  #Tautology    : 74
% 6.59/2.45  #SimpNegUnit  : 26
% 6.59/2.45  #BackRed      : 8
% 6.59/2.45  
% 6.59/2.45  #Partial instantiations: 0
% 6.59/2.45  #Strategies tried      : 1
% 6.59/2.45  
% 6.59/2.45  Timing (in seconds)
% 6.59/2.45  ----------------------
% 6.59/2.45  Preprocessing        : 0.38
% 6.59/2.45  Parsing              : 0.20
% 6.59/2.45  CNF conversion       : 0.03
% 6.59/2.45  Main loop            : 1.22
% 6.59/2.45  Inferencing          : 0.38
% 6.59/2.45  Reduction            : 0.27
% 6.59/2.45  Demodulation         : 0.16
% 6.59/2.45  BG Simplification    : 0.04
% 6.59/2.45  Subsumption          : 0.43
% 6.59/2.45  Abstraction          : 0.05
% 6.59/2.45  MUC search           : 0.00
% 6.59/2.45  Cooper               : 0.00
% 6.59/2.45  Total                : 1.63
% 6.59/2.45  Index Insertion      : 0.00
% 6.59/2.45  Index Deletion       : 0.00
% 6.59/2.45  Index Matching       : 0.00
% 6.59/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
