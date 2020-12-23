%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:50 EST 2020

% Result     : Theorem 16.59s
% Output     : CNFRefutation 16.59s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 814 expanded)
%              Number of leaves         :   22 ( 285 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 (1875 expanded)
%              Number of equality atoms :   21 ( 402 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,(
    ! [A_43,B_44] :
      ( k1_tops_1(A_43,k1_tops_1(A_43,B_44)) = k1_tops_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_83,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_58,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k1_tops_1(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( r1_tarski(B_9,k2_pre_topc(A_7,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_166,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tops_1(A_54,B_55),k2_pre_topc(A_54,k1_tops_1(A_54,B_55)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_58,c_12])).

tff(c_171,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_166])).

tff(c_177,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_83,c_171])).

tff(c_194,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_211,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_194])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_211])).

tff(c_217,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_pre_topc(A_5,k2_pre_topc(A_5,B_6)) = k2_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_217,c_10])).

tff(c_228,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_219])).

tff(c_65,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k2_pre_topc(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k1_tops_1(A_21,B_23),B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_tops_1(A_41,k2_pre_topc(A_41,B_42)),k2_pre_topc(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_65,c_20])).

tff(c_250,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_70])).

tff(c_268,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_228,c_250])).

tff(c_1103,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_1106,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1103])).

tff(c_1110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_217,c_1106])).

tff(c_1112,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_216,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_114,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k1_tops_1(A_47,B_48),k1_tops_1(A_47,C_49))
      | ~ r1_tarski(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_119,plain,(
    ! [C_49] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_49))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_114])).

tff(c_125,plain,(
    ! [C_49] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_49))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_119])).

tff(c_1609,plain,(
    ! [C_49] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_49))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_125])).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) != k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_538,plain,(
    ! [A_73,B_74] :
      ( k1_tops_1(A_73,k1_tops_1(A_73,k2_pre_topc(A_73,B_74))) = k1_tops_1(A_73,k2_pre_topc(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_542,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_217,c_538])).

tff(c_554,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_542])).

tff(c_2183,plain,(
    ! [A_104,B_105] :
      ( k1_tops_1(A_104,k1_tops_1(A_104,k2_pre_topc(A_104,k1_tops_1(A_104,B_105)))) = k1_tops_1(A_104,k2_pre_topc(A_104,k1_tops_1(A_104,B_105)))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_16,c_538])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tops_1(A_39,B_40),k2_pre_topc(A_39,k1_tops_1(A_39,B_40)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_58,c_12])).

tff(c_2770,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k1_tops_1(A_119,k2_pre_topc(A_119,k1_tops_1(A_119,B_120))),k2_pre_topc(A_119,k1_tops_1(A_119,k1_tops_1(A_119,k2_pre_topc(A_119,k1_tops_1(A_119,B_120))))))
      | ~ m1_subset_1(k1_tops_1(A_119,k2_pre_topc(A_119,k1_tops_1(A_119,B_120))),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2183,c_64])).

tff(c_2830,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2770])).

tff(c_2854,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_217,c_28,c_83,c_554,c_83,c_2830])).

tff(c_2873,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2854])).

tff(c_2897,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_2873])).

tff(c_2901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1112,c_2897])).

tff(c_2903,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2854])).

tff(c_1111,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_308,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k2_pre_topc(A_61,B_62),k2_pre_topc(A_61,C_63))
      | ~ r1_tarski(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_316,plain,(
    ! [B_62] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_62),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(B_62,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_308])).

tff(c_327,plain,(
    ! [B_62] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_62),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(B_62,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_316])).

tff(c_30457,plain,(
    ! [B_328] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_328),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(B_328,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_327])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_323,plain,(
    ! [A_61,C_63,B_62] :
      ( k2_pre_topc(A_61,C_63) = k2_pre_topc(A_61,B_62)
      | ~ r1_tarski(k2_pre_topc(A_61,C_63),k2_pre_topc(A_61,B_62))
      | ~ r1_tarski(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_308,c_2])).

tff(c_30503,plain,(
    ! [B_328] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',B_328)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_328)
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_328,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_30457,c_323])).

tff(c_30626,plain,(
    ! [B_329] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',B_329)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_329)
      | ~ r1_tarski(B_329,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_217,c_30503])).

tff(c_30632,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1111,c_30626])).

tff(c_30659,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2903,c_30632])).

tff(c_30660,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_30659])).

tff(c_30817,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1609,c_30660])).

tff(c_30824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_216,c_30817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.59/7.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.59/7.77  
% 16.59/7.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.59/7.77  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 16.59/7.77  
% 16.59/7.77  %Foreground sorts:
% 16.59/7.77  
% 16.59/7.77  
% 16.59/7.77  %Background operators:
% 16.59/7.77  
% 16.59/7.77  
% 16.59/7.77  %Foreground operators:
% 16.59/7.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.59/7.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.59/7.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.59/7.77  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.59/7.77  tff('#skF_2', type, '#skF_2': $i).
% 16.59/7.77  tff('#skF_1', type, '#skF_1': $i).
% 16.59/7.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.59/7.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.59/7.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.59/7.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.59/7.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 16.59/7.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.59/7.77  
% 16.59/7.78  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 16.59/7.78  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 16.59/7.78  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 16.59/7.78  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 16.59/7.78  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 16.59/7.78  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 16.59/7.78  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 16.59/7.78  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 16.59/7.78  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 16.59/7.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.59/7.78  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.59/7.78  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.59/7.78  tff(c_16, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.59/7.78  tff(c_72, plain, (![A_43, B_44]: (k1_tops_1(A_43, k1_tops_1(A_43, B_44))=k1_tops_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.59/7.78  tff(c_78, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_72])).
% 16.59/7.78  tff(c_83, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_78])).
% 16.59/7.78  tff(c_58, plain, (![A_39, B_40]: (m1_subset_1(k1_tops_1(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.59/7.78  tff(c_12, plain, (![B_9, A_7]: (r1_tarski(B_9, k2_pre_topc(A_7, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.59/7.78  tff(c_166, plain, (![A_54, B_55]: (r1_tarski(k1_tops_1(A_54, B_55), k2_pre_topc(A_54, k1_tops_1(A_54, B_55))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_58, c_12])).
% 16.59/7.78  tff(c_171, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83, c_166])).
% 16.59/7.78  tff(c_177, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_83, c_171])).
% 16.59/7.78  tff(c_194, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_177])).
% 16.59/7.78  tff(c_211, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_194])).
% 16.59/7.78  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_211])).
% 16.59/7.78  tff(c_217, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_177])).
% 16.59/7.78  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.59/7.78  tff(c_10, plain, (![A_5, B_6]: (k2_pre_topc(A_5, k2_pre_topc(A_5, B_6))=k2_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.59/7.78  tff(c_219, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_217, c_10])).
% 16.59/7.78  tff(c_228, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_219])).
% 16.59/7.79  tff(c_65, plain, (![A_41, B_42]: (m1_subset_1(k2_pre_topc(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.59/7.79  tff(c_20, plain, (![A_21, B_23]: (r1_tarski(k1_tops_1(A_21, B_23), B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.59/7.79  tff(c_70, plain, (![A_41, B_42]: (r1_tarski(k1_tops_1(A_41, k2_pre_topc(A_41, B_42)), k2_pre_topc(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_65, c_20])).
% 16.59/7.79  tff(c_250, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_228, c_70])).
% 16.59/7.79  tff(c_268, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_228, c_250])).
% 16.59/7.79  tff(c_1103, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_268])).
% 16.59/7.79  tff(c_1106, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_1103])).
% 16.59/7.79  tff(c_1110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_217, c_1106])).
% 16.59/7.79  tff(c_1112, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_268])).
% 16.59/7.79  tff(c_216, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_177])).
% 16.59/7.79  tff(c_114, plain, (![A_47, B_48, C_49]: (r1_tarski(k1_tops_1(A_47, B_48), k1_tops_1(A_47, C_49)) | ~r1_tarski(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.59/7.79  tff(c_119, plain, (![C_49]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_49)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_114])).
% 16.59/7.79  tff(c_125, plain, (![C_49]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_49)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_119])).
% 16.59/7.79  tff(c_1609, plain, (![C_49]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_49)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_125])).
% 16.59/7.79  tff(c_24, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))!=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.59/7.79  tff(c_538, plain, (![A_73, B_74]: (k1_tops_1(A_73, k1_tops_1(A_73, k2_pre_topc(A_73, B_74)))=k1_tops_1(A_73, k2_pre_topc(A_73, B_74)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_8, c_72])).
% 16.59/7.79  tff(c_542, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_217, c_538])).
% 16.59/7.79  tff(c_554, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_542])).
% 16.59/7.79  tff(c_2183, plain, (![A_104, B_105]: (k1_tops_1(A_104, k1_tops_1(A_104, k2_pre_topc(A_104, k1_tops_1(A_104, B_105))))=k1_tops_1(A_104, k2_pre_topc(A_104, k1_tops_1(A_104, B_105))) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_16, c_538])).
% 16.59/7.79  tff(c_64, plain, (![A_39, B_40]: (r1_tarski(k1_tops_1(A_39, B_40), k2_pre_topc(A_39, k1_tops_1(A_39, B_40))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_58, c_12])).
% 16.59/7.79  tff(c_2770, plain, (![A_119, B_120]: (r1_tarski(k1_tops_1(A_119, k2_pre_topc(A_119, k1_tops_1(A_119, B_120))), k2_pre_topc(A_119, k1_tops_1(A_119, k1_tops_1(A_119, k2_pre_topc(A_119, k1_tops_1(A_119, B_120)))))) | ~m1_subset_1(k1_tops_1(A_119, k2_pre_topc(A_119, k1_tops_1(A_119, B_120))), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(superposition, [status(thm), theory('equality')], [c_2183, c_64])).
% 16.59/7.79  tff(c_2830, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83, c_2770])).
% 16.59/7.79  tff(c_2854, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_217, c_28, c_83, c_554, c_83, c_2830])).
% 16.59/7.79  tff(c_2873, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2854])).
% 16.59/7.79  tff(c_2897, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_2873])).
% 16.59/7.79  tff(c_2901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1112, c_2897])).
% 16.59/7.79  tff(c_2903, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2854])).
% 16.59/7.79  tff(c_1111, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_268])).
% 16.59/7.79  tff(c_308, plain, (![A_61, B_62, C_63]: (r1_tarski(k2_pre_topc(A_61, B_62), k2_pre_topc(A_61, C_63)) | ~r1_tarski(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.59/7.79  tff(c_316, plain, (![B_62]: (r1_tarski(k2_pre_topc('#skF_1', B_62), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(B_62, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_308])).
% 16.59/7.79  tff(c_327, plain, (![B_62]: (r1_tarski(k2_pre_topc('#skF_1', B_62), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(B_62, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_316])).
% 16.59/7.79  tff(c_30457, plain, (![B_328]: (r1_tarski(k2_pre_topc('#skF_1', B_328), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(B_328, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_327])).
% 16.59/7.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.59/7.79  tff(c_323, plain, (![A_61, C_63, B_62]: (k2_pre_topc(A_61, C_63)=k2_pre_topc(A_61, B_62) | ~r1_tarski(k2_pre_topc(A_61, C_63), k2_pre_topc(A_61, B_62)) | ~r1_tarski(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_308, c_2])).
% 16.59/7.79  tff(c_30503, plain, (![B_328]: (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', B_328) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_328) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_328, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_30457, c_323])).
% 16.59/7.79  tff(c_30626, plain, (![B_329]: (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', B_329) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_329) | ~r1_tarski(B_329, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_217, c_30503])).
% 16.59/7.79  tff(c_30632, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1111, c_30626])).
% 16.59/7.79  tff(c_30659, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2903, c_30632])).
% 16.59/7.79  tff(c_30660, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_24, c_30659])).
% 16.59/7.79  tff(c_30817, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1609, c_30660])).
% 16.59/7.79  tff(c_30824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1112, c_216, c_30817])).
% 16.59/7.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.59/7.79  
% 16.59/7.79  Inference rules
% 16.59/7.79  ----------------------
% 16.59/7.79  #Ref     : 0
% 16.59/7.79  #Sup     : 6524
% 16.59/7.79  #Fact    : 0
% 16.59/7.79  #Define  : 0
% 16.59/7.79  #Split   : 29
% 16.59/7.79  #Chain   : 0
% 16.59/7.79  #Close   : 0
% 16.59/7.79  
% 16.59/7.79  Ordering : KBO
% 16.59/7.79  
% 16.59/7.79  Simplification rules
% 16.59/7.79  ----------------------
% 16.59/7.79  #Subsume      : 1622
% 16.59/7.79  #Demod        : 16078
% 16.59/7.79  #Tautology    : 1290
% 16.59/7.79  #SimpNegUnit  : 25
% 16.59/7.79  #BackRed      : 3
% 16.59/7.79  
% 16.59/7.79  #Partial instantiations: 0
% 16.59/7.79  #Strategies tried      : 1
% 16.59/7.79  
% 16.59/7.79  Timing (in seconds)
% 16.59/7.79  ----------------------
% 16.59/7.79  Preprocessing        : 0.30
% 16.59/7.79  Parsing              : 0.17
% 16.59/7.79  CNF conversion       : 0.02
% 16.59/7.79  Main loop            : 6.71
% 16.59/7.79  Inferencing          : 1.06
% 16.59/7.79  Reduction            : 2.15
% 16.59/7.79  Demodulation         : 1.70
% 16.59/7.79  BG Simplification    : 0.15
% 16.59/7.79  Subsumption          : 3.14
% 16.59/7.79  Abstraction          : 0.26
% 16.59/7.79  MUC search           : 0.00
% 16.59/7.79  Cooper               : 0.00
% 16.59/7.79  Total                : 7.04
% 16.59/7.79  Index Insertion      : 0.00
% 16.59/7.79  Index Deletion       : 0.00
% 16.59/7.79  Index Matching       : 0.00
% 16.59/7.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
