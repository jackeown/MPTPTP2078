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
% DateTime   : Thu Dec  3 10:20:23 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 240 expanded)
%              Number of leaves         :   37 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  138 ( 433 expanded)
%              Number of equality atoms :   24 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_62,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
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

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_46,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [A_25] :
      ( v1_xboole_0(k1_struct_0(A_25))
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_65,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_65])).

tff(c_82,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = k1_xboole_0
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_87,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_91,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_167,plain,(
    ! [A_60] :
      ( k3_subset_1(u1_struct_0(A_60),k1_struct_0(A_60)) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_176,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_167])).

tff(c_187,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_190,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_190])).

tff(c_196,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_20,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_161,plain,(
    ! [B_58,A_59] :
      ( ~ r1_tarski(B_58,'#skF_1'(A_59,B_58))
      | r1_xboole_0(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_119,c_32])).

tff(c_166,plain,(
    ! [A_59] : r1_xboole_0(A_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_161])).

tff(c_195,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_378,plain,(
    ! [B_101,A_102,C_103] :
      ( r1_tarski(B_101,k3_subset_1(A_102,C_103))
      | ~ r1_xboole_0(B_101,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_393,plain,(
    ! [B_101] :
      ( r1_tarski(B_101,k2_struct_0('#skF_2'))
      | ~ r1_xboole_0(B_101,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_378])).

tff(c_402,plain,(
    ! [B_101] :
      ( r1_tarski(B_101,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_393])).

tff(c_424,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_427,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_424])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_427])).

tff(c_444,plain,(
    ! [B_107] :
      ( r1_tarski(B_107,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_473,plain,(
    r1_tarski(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_49,c_444])).

tff(c_152,plain,(
    ! [A_56] :
      ( m1_subset_1(k2_struct_0(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_157,plain,(
    ! [A_57] :
      ( r1_tarski(k2_struct_0(A_57),u1_struct_0(A_57))
      | ~ l1_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_152,c_28])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_160,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ r1_tarski(u1_struct_0(A_57),k2_struct_0(A_57))
      | ~ l1_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_157,c_10])).

tff(c_476,plain,
    ( u1_struct_0('#skF_2') = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_473,c_160])).

tff(c_481,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_476])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_289,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k2_pre_topc(A_86,B_87),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_296,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_pre_topc(A_86,B_87),u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_289,c_28])).

tff(c_260,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,k2_pre_topc(A_79,B_78))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_281,plain,(
    ! [A_83,A_84] :
      ( r1_tarski(A_83,k2_pre_topc(A_84,A_83))
      | ~ l1_pre_topc(A_84)
      | ~ r1_tarski(A_83,u1_struct_0(A_84)) ) ),
    inference(resolution,[status(thm)],[c_30,c_260])).

tff(c_302,plain,(
    ! [A_91,A_92] :
      ( k2_pre_topc(A_91,A_92) = A_92
      | ~ r1_tarski(k2_pre_topc(A_91,A_92),A_92)
      | ~ l1_pre_topc(A_91)
      | ~ r1_tarski(A_92,u1_struct_0(A_91)) ) ),
    inference(resolution,[status(thm)],[c_281,c_10])).

tff(c_306,plain,(
    ! [A_86] :
      ( k2_pre_topc(A_86,u1_struct_0(A_86)) = u1_struct_0(A_86)
      | ~ r1_tarski(u1_struct_0(A_86),u1_struct_0(A_86))
      | ~ m1_subset_1(u1_struct_0(A_86),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_296,c_302])).

tff(c_309,plain,(
    ! [A_86] :
      ( k2_pre_topc(A_86,u1_struct_0(A_86)) = u1_struct_0(A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_14,c_306])).

tff(c_497,plain,
    ( k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_309])).

tff(c_531,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_481,c_497])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.34  
% 2.59/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 2.59/1.35  
% 2.59/1.35  %Foreground sorts:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Background operators:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Foreground operators:
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.59/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.35  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.59/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.59/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.59/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.59/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.35  
% 2.79/1.36  tff(f_116, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 2.79/1.36  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.79/1.36  tff(f_100, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.79/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.79/1.36  tff(f_60, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.79/1.36  tff(f_104, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.79/1.36  tff(f_62, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.79/1.36  tff(f_64, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.79/1.36  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.79/1.36  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.36  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.79/1.36  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.79/1.36  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.79/1.36  tff(f_92, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.79/1.36  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.36  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.79/1.36  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.79/1.36  tff(c_46, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.79/1.36  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.79/1.36  tff(c_38, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.36  tff(c_40, plain, (![A_25]: (v1_xboole_0(k1_struct_0(A_25)) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.79/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.79/1.36  tff(c_65, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.36  tff(c_72, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_2, c_65])).
% 2.79/1.36  tff(c_82, plain, (![A_39]: (k1_struct_0(A_39)=k1_xboole_0 | ~l1_struct_0(A_39))), inference(resolution, [status(thm)], [c_40, c_72])).
% 2.79/1.36  tff(c_87, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_38, c_82])).
% 2.79/1.36  tff(c_91, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_87])).
% 2.79/1.36  tff(c_167, plain, (![A_60]: (k3_subset_1(u1_struct_0(A_60), k1_struct_0(A_60))=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.79/1.36  tff(c_176, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_167])).
% 2.79/1.36  tff(c_187, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_176])).
% 2.79/1.36  tff(c_190, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_187])).
% 2.79/1.36  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_190])).
% 2.79/1.36  tff(c_196, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_176])).
% 2.79/1.36  tff(c_20, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.36  tff(c_22, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.79/1.36  tff(c_49, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.79/1.36  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.79/1.36  tff(c_30, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.36  tff(c_119, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.79/1.36  tff(c_32, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.36  tff(c_161, plain, (![B_58, A_59]: (~r1_tarski(B_58, '#skF_1'(A_59, B_58)) | r1_xboole_0(A_59, B_58))), inference(resolution, [status(thm)], [c_119, c_32])).
% 2.79/1.36  tff(c_166, plain, (![A_59]: (r1_xboole_0(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_161])).
% 2.79/1.36  tff(c_195, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_176])).
% 2.79/1.36  tff(c_378, plain, (![B_101, A_102, C_103]: (r1_tarski(B_101, k3_subset_1(A_102, C_103)) | ~r1_xboole_0(B_101, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_102)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.36  tff(c_393, plain, (![B_101]: (r1_tarski(B_101, k2_struct_0('#skF_2')) | ~r1_xboole_0(B_101, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_195, c_378])).
% 2.79/1.36  tff(c_402, plain, (![B_101]: (r1_tarski(B_101, k2_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_393])).
% 2.79/1.36  tff(c_424, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_402])).
% 2.79/1.36  tff(c_427, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_424])).
% 2.79/1.36  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_427])).
% 2.79/1.36  tff(c_444, plain, (![B_107]: (r1_tarski(B_107, k2_struct_0('#skF_2')) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_402])).
% 2.79/1.36  tff(c_473, plain, (r1_tarski(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_49, c_444])).
% 2.79/1.36  tff(c_152, plain, (![A_56]: (m1_subset_1(k2_struct_0(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.36  tff(c_28, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.36  tff(c_157, plain, (![A_57]: (r1_tarski(k2_struct_0(A_57), u1_struct_0(A_57)) | ~l1_struct_0(A_57))), inference(resolution, [status(thm)], [c_152, c_28])).
% 2.79/1.36  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.36  tff(c_160, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~r1_tarski(u1_struct_0(A_57), k2_struct_0(A_57)) | ~l1_struct_0(A_57))), inference(resolution, [status(thm)], [c_157, c_10])).
% 2.79/1.36  tff(c_476, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_473, c_160])).
% 2.79/1.36  tff(c_481, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_476])).
% 2.79/1.36  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.36  tff(c_289, plain, (![A_86, B_87]: (m1_subset_1(k2_pre_topc(A_86, B_87), k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.36  tff(c_296, plain, (![A_86, B_87]: (r1_tarski(k2_pre_topc(A_86, B_87), u1_struct_0(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_289, c_28])).
% 2.79/1.36  tff(c_260, plain, (![B_78, A_79]: (r1_tarski(B_78, k2_pre_topc(A_79, B_78)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.79/1.36  tff(c_281, plain, (![A_83, A_84]: (r1_tarski(A_83, k2_pre_topc(A_84, A_83)) | ~l1_pre_topc(A_84) | ~r1_tarski(A_83, u1_struct_0(A_84)))), inference(resolution, [status(thm)], [c_30, c_260])).
% 2.79/1.36  tff(c_302, plain, (![A_91, A_92]: (k2_pre_topc(A_91, A_92)=A_92 | ~r1_tarski(k2_pre_topc(A_91, A_92), A_92) | ~l1_pre_topc(A_91) | ~r1_tarski(A_92, u1_struct_0(A_91)))), inference(resolution, [status(thm)], [c_281, c_10])).
% 2.79/1.36  tff(c_306, plain, (![A_86]: (k2_pre_topc(A_86, u1_struct_0(A_86))=u1_struct_0(A_86) | ~r1_tarski(u1_struct_0(A_86), u1_struct_0(A_86)) | ~m1_subset_1(u1_struct_0(A_86), k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_296, c_302])).
% 2.79/1.36  tff(c_309, plain, (![A_86]: (k2_pre_topc(A_86, u1_struct_0(A_86))=u1_struct_0(A_86) | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_14, c_306])).
% 2.79/1.36  tff(c_497, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_481, c_309])).
% 2.79/1.36  tff(c_531, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_481, c_497])).
% 2.79/1.36  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_531])).
% 2.79/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.36  
% 2.79/1.36  Inference rules
% 2.79/1.36  ----------------------
% 2.79/1.36  #Ref     : 0
% 2.79/1.36  #Sup     : 106
% 2.79/1.36  #Fact    : 0
% 2.79/1.36  #Define  : 0
% 2.79/1.36  #Split   : 2
% 2.79/1.36  #Chain   : 0
% 2.79/1.36  #Close   : 0
% 2.79/1.36  
% 2.79/1.36  Ordering : KBO
% 2.79/1.36  
% 2.79/1.36  Simplification rules
% 2.79/1.36  ----------------------
% 2.79/1.36  #Subsume      : 10
% 2.79/1.36  #Demod        : 53
% 2.79/1.36  #Tautology    : 39
% 2.79/1.36  #SimpNegUnit  : 1
% 2.79/1.36  #BackRed      : 4
% 2.79/1.36  
% 2.79/1.36  #Partial instantiations: 0
% 2.79/1.36  #Strategies tried      : 1
% 2.79/1.36  
% 2.79/1.36  Timing (in seconds)
% 2.79/1.36  ----------------------
% 2.79/1.37  Preprocessing        : 0.30
% 2.79/1.37  Parsing              : 0.17
% 2.79/1.37  CNF conversion       : 0.02
% 2.79/1.37  Main loop            : 0.29
% 2.79/1.37  Inferencing          : 0.11
% 2.79/1.37  Reduction            : 0.08
% 2.79/1.37  Demodulation         : 0.05
% 2.79/1.37  BG Simplification    : 0.02
% 2.79/1.37  Subsumption          : 0.06
% 2.79/1.37  Abstraction          : 0.01
% 2.79/1.37  MUC search           : 0.00
% 2.79/1.37  Cooper               : 0.00
% 2.79/1.37  Total                : 0.62
% 2.79/1.37  Index Insertion      : 0.00
% 2.79/1.37  Index Deletion       : 0.00
% 2.79/1.37  Index Matching       : 0.00
% 2.79/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
