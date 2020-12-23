%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:02 EST 2020

% Result     : Theorem 9.16s
% Output     : CNFRefutation 9.28s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  169 ( 296 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( r2_hidden(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( v4_pre_topc(D,A)
                        & r1_tarski(B,D) )
                     => r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_pre_topc(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54,C_55),C_55)
      | r1_tarski(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_67,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_1'(A_50,B_51,C_52),B_51)
      | r1_tarski(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_68,B_69,C_70,A_71] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),A_71)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_71))
      | r1_tarski(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_222,plain,(
    ! [A_108,C_104,A_106,A_107,B_105] :
      ( r2_hidden('#skF_1'(A_108,B_105,C_104),A_107)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_106))
      | r1_tarski(B_105,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_328,plain,(
    ! [B_126,A_128,B_124,C_127,A_125] :
      ( r2_hidden('#skF_1'(A_128,B_126,C_127),B_124)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125))
      | r1_tarski(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_128))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_128))
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(resolution,[status(thm)],[c_12,c_222])).

tff(c_412,plain,(
    ! [C_143,A_145,A_144,B_142,B_146] :
      ( r2_hidden('#skF_1'(A_145,A_144,C_143),B_146)
      | r1_tarski(A_144,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(A_144,k1_zfmisc_1(A_145))
      | ~ r1_tarski(B_142,B_146)
      | ~ r1_tarski(A_144,B_142) ) ),
    inference(resolution,[status(thm)],[c_12,c_328])).

tff(c_436,plain,(
    ! [A_145,A_144,C_143] :
      ( r2_hidden('#skF_1'(A_145,A_144,C_143),u1_struct_0('#skF_3'))
      | r1_tarski(A_144,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(A_144,k1_zfmisc_1(A_145))
      | ~ r1_tarski(A_144,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_412])).

tff(c_51,plain,(
    ! [A_50,B_51,C_52,A_1] :
      ( r2_hidden('#skF_1'(A_50,B_51,C_52),A_1)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_1))
      | r1_tarski(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_107,plain,(
    ! [B_72,A_73,C_74] :
      ( r1_tarski(B_72,'#skF_2'(A_73,B_72,C_74))
      | r2_hidden(C_74,k2_pre_topc(A_73,B_72))
      | ~ r2_hidden(C_74,u1_struct_0(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_117,plain,(
    ! [C_74] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4',C_74))
      | r2_hidden(C_74,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden(C_74,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_124,plain,(
    ! [C_75] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4',C_75))
      | r2_hidden(C_75,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden(C_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_117])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_203,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(B_96,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97))
      | r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_1'(A_97,B_96,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ r2_hidden('#skF_1'(A_97,B_96,k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_124,c_4])).

tff(c_212,plain,(
    ! [A_50,B_51] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_1'(A_50,B_51,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(B_51,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_51,c_203])).

tff(c_165,plain,(
    ! [C_83,A_84,B_85] :
      ( ~ r2_hidden(C_83,'#skF_2'(A_84,B_85,C_83))
      | r2_hidden(C_83,k2_pre_topc(A_84,B_85))
      | ~ r2_hidden(C_83,u1_struct_0(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1439,plain,(
    ! [A_350,B_354,A_351,C_352,B_353] :
      ( r2_hidden('#skF_1'(A_350,B_354,C_352),k2_pre_topc(A_351,B_353))
      | ~ r2_hidden('#skF_1'(A_350,B_354,C_352),u1_struct_0(A_351))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351)
      | ~ m1_subset_1(B_354,k1_zfmisc_1('#skF_2'(A_351,B_353,'#skF_1'(A_350,B_354,C_352))))
      | r1_tarski(B_354,C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(A_350))
      | ~ m1_subset_1(B_354,k1_zfmisc_1(A_350)) ) ),
    inference(resolution,[status(thm)],[c_51,c_165])).

tff(c_4712,plain,(
    ! [B_747,A_744,A_745,A_746,C_743] :
      ( r2_hidden('#skF_1'(A_745,A_744,C_743),k2_pre_topc(A_746,B_747))
      | ~ r2_hidden('#skF_1'(A_745,A_744,C_743),u1_struct_0(A_746))
      | ~ m1_subset_1(B_747,k1_zfmisc_1(u1_struct_0(A_746)))
      | ~ l1_pre_topc(A_746)
      | r1_tarski(A_744,C_743)
      | ~ m1_subset_1(C_743,k1_zfmisc_1(A_745))
      | ~ m1_subset_1(A_744,k1_zfmisc_1(A_745))
      | ~ r1_tarski(A_744,'#skF_2'(A_746,B_747,'#skF_1'(A_745,A_744,C_743))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1439])).

tff(c_4754,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_50,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_50))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_212,c_4712])).

tff(c_4808,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_50,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_50))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_50)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4754])).

tff(c_4828,plain,(
    ! [A_748] :
      ( r2_hidden('#skF_1'(A_748,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_748,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_748))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_748)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4808])).

tff(c_4839,plain,(
    ! [A_748] :
      ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_748,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_748))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_748)) ) ),
    inference(resolution,[status(thm)],[c_4828,c_4])).

tff(c_4856,plain,(
    ! [A_749] :
      ( ~ r2_hidden('#skF_1'(A_749,'#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_749))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_749)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4839])).

tff(c_4884,plain,(
    ! [A_145] :
      ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_145))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_145))
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_436,c_4856])).

tff(c_4920,plain,(
    ! [A_145] :
      ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_145))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_145)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_4884])).

tff(c_4931,plain,(
    ! [A_750] :
      ( ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(A_750))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_750)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4920])).

tff(c_4935,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_4931])).

tff(c_4943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_4935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.16/3.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.28/3.59  
% 9.28/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.28/3.59  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 9.28/3.59  
% 9.28/3.59  %Foreground sorts:
% 9.28/3.59  
% 9.28/3.59  
% 9.28/3.59  %Background operators:
% 9.28/3.59  
% 9.28/3.59  
% 9.28/3.59  %Foreground operators:
% 9.28/3.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.28/3.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.28/3.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.28/3.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.28/3.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.28/3.59  tff('#skF_3', type, '#skF_3': $i).
% 9.28/3.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.28/3.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.28/3.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.28/3.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.28/3.59  tff('#skF_4', type, '#skF_4': $i).
% 9.28/3.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.28/3.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.28/3.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.28/3.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.28/3.59  
% 9.28/3.61  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 9.28/3.61  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.28/3.61  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 9.28/3.61  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.28/3.61  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.28/3.61  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_pre_topc)).
% 9.28/3.61  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.28/3.61  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.28/3.61  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(k2_pre_topc(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.28/3.61  tff(c_26, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.28/3.61  tff(c_6, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.28/3.61  tff(c_52, plain, (![A_53, B_54, C_55]: (~r2_hidden('#skF_1'(A_53, B_54, C_55), C_55) | r1_tarski(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.28/3.61  tff(c_58, plain, (![B_56, A_57]: (r1_tarski(B_56, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_6, c_52])).
% 9.28/3.61  tff(c_67, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_58])).
% 9.28/3.61  tff(c_32, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.28/3.61  tff(c_40, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_32])).
% 9.28/3.61  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.28/3.61  tff(c_48, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_1'(A_50, B_51, C_52), B_51) | r1_tarski(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.28/3.61  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.28/3.61  tff(c_98, plain, (![A_68, B_69, C_70, A_71]: (r2_hidden('#skF_1'(A_68, B_69, C_70), A_71) | ~m1_subset_1(B_69, k1_zfmisc_1(A_71)) | r1_tarski(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_48, c_2])).
% 9.28/3.61  tff(c_222, plain, (![A_108, C_104, A_106, A_107, B_105]: (r2_hidden('#skF_1'(A_108, B_105, C_104), A_107) | ~m1_subset_1(A_106, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_106)) | r1_tarski(B_105, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_108)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_98, c_2])).
% 9.28/3.61  tff(c_328, plain, (![B_126, A_128, B_124, C_127, A_125]: (r2_hidden('#skF_1'(A_128, B_126, C_127), B_124) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)) | r1_tarski(B_126, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_128)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_128)) | ~r1_tarski(A_125, B_124))), inference(resolution, [status(thm)], [c_12, c_222])).
% 9.28/3.61  tff(c_412, plain, (![C_143, A_145, A_144, B_142, B_146]: (r2_hidden('#skF_1'(A_145, A_144, C_143), B_146) | r1_tarski(A_144, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(A_145)) | ~m1_subset_1(A_144, k1_zfmisc_1(A_145)) | ~r1_tarski(B_142, B_146) | ~r1_tarski(A_144, B_142))), inference(resolution, [status(thm)], [c_12, c_328])).
% 9.28/3.61  tff(c_436, plain, (![A_145, A_144, C_143]: (r2_hidden('#skF_1'(A_145, A_144, C_143), u1_struct_0('#skF_3')) | r1_tarski(A_144, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(A_145)) | ~m1_subset_1(A_144, k1_zfmisc_1(A_145)) | ~r1_tarski(A_144, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_412])).
% 9.28/3.61  tff(c_51, plain, (![A_50, B_51, C_52, A_1]: (r2_hidden('#skF_1'(A_50, B_51, C_52), A_1) | ~m1_subset_1(B_51, k1_zfmisc_1(A_1)) | r1_tarski(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_48, c_2])).
% 9.28/3.61  tff(c_107, plain, (![B_72, A_73, C_74]: (r1_tarski(B_72, '#skF_2'(A_73, B_72, C_74)) | r2_hidden(C_74, k2_pre_topc(A_73, B_72)) | ~r2_hidden(C_74, u1_struct_0(A_73)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.28/3.61  tff(c_117, plain, (![C_74]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', C_74)) | r2_hidden(C_74, k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden(C_74, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_107])).
% 9.28/3.61  tff(c_124, plain, (![C_75]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', C_75)) | r2_hidden(C_75, k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden(C_75, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_117])).
% 9.28/3.61  tff(c_4, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.28/3.61  tff(c_203, plain, (![B_96, A_97]: (r1_tarski(B_96, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_97)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)) | r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_97, B_96, k2_pre_topc('#skF_3', '#skF_4')))) | ~r2_hidden('#skF_1'(A_97, B_96, k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_124, c_4])).
% 9.28/3.61  tff(c_212, plain, (![A_50, B_51]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_50, B_51, k2_pre_topc('#skF_3', '#skF_4')))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(B_51, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_51, c_203])).
% 9.28/3.61  tff(c_165, plain, (![C_83, A_84, B_85]: (~r2_hidden(C_83, '#skF_2'(A_84, B_85, C_83)) | r2_hidden(C_83, k2_pre_topc(A_84, B_85)) | ~r2_hidden(C_83, u1_struct_0(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.28/3.61  tff(c_1439, plain, (![A_350, B_354, A_351, C_352, B_353]: (r2_hidden('#skF_1'(A_350, B_354, C_352), k2_pre_topc(A_351, B_353)) | ~r2_hidden('#skF_1'(A_350, B_354, C_352), u1_struct_0(A_351)) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351) | ~m1_subset_1(B_354, k1_zfmisc_1('#skF_2'(A_351, B_353, '#skF_1'(A_350, B_354, C_352)))) | r1_tarski(B_354, C_352) | ~m1_subset_1(C_352, k1_zfmisc_1(A_350)) | ~m1_subset_1(B_354, k1_zfmisc_1(A_350)))), inference(resolution, [status(thm)], [c_51, c_165])).
% 9.28/3.61  tff(c_4712, plain, (![B_747, A_744, A_745, A_746, C_743]: (r2_hidden('#skF_1'(A_745, A_744, C_743), k2_pre_topc(A_746, B_747)) | ~r2_hidden('#skF_1'(A_745, A_744, C_743), u1_struct_0(A_746)) | ~m1_subset_1(B_747, k1_zfmisc_1(u1_struct_0(A_746))) | ~l1_pre_topc(A_746) | r1_tarski(A_744, C_743) | ~m1_subset_1(C_743, k1_zfmisc_1(A_745)) | ~m1_subset_1(A_744, k1_zfmisc_1(A_745)) | ~r1_tarski(A_744, '#skF_2'(A_746, B_747, '#skF_1'(A_745, A_744, C_743))))), inference(resolution, [status(thm)], [c_12, c_1439])).
% 9.28/3.61  tff(c_4754, plain, (![A_50]: (r2_hidden('#skF_1'(A_50, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_50, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_50)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_212, c_4712])).
% 9.28/3.61  tff(c_4808, plain, (![A_50]: (r2_hidden('#skF_1'(A_50, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_50, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_50)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4754])).
% 9.28/3.61  tff(c_4828, plain, (![A_748]: (r2_hidden('#skF_1'(A_748, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_748, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_748)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_748)))), inference(negUnitSimplification, [status(thm)], [c_26, c_4808])).
% 9.28/3.61  tff(c_4839, plain, (![A_748]: (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_748, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_748)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_748)))), inference(resolution, [status(thm)], [c_4828, c_4])).
% 9.28/3.61  tff(c_4856, plain, (![A_749]: (~r2_hidden('#skF_1'(A_749, '#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_749)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_749)))), inference(negUnitSimplification, [status(thm)], [c_26, c_4839])).
% 9.28/3.61  tff(c_4884, plain, (![A_145]: (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_145)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_145)) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_436, c_4856])).
% 9.28/3.61  tff(c_4920, plain, (![A_145]: (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_145)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_145)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_4884])).
% 9.28/3.61  tff(c_4931, plain, (![A_750]: (~m1_subset_1(k2_pre_topc('#skF_3', '#skF_4'), k1_zfmisc_1(A_750)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_750)))), inference(negUnitSimplification, [status(thm)], [c_26, c_4920])).
% 9.28/3.61  tff(c_4935, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_4931])).
% 9.28/3.61  tff(c_4943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_4935])).
% 9.28/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.28/3.61  
% 9.28/3.61  Inference rules
% 9.28/3.61  ----------------------
% 9.28/3.61  #Ref     : 0
% 9.28/3.61  #Sup     : 1210
% 9.28/3.61  #Fact    : 0
% 9.28/3.61  #Define  : 0
% 9.28/3.61  #Split   : 8
% 9.28/3.61  #Chain   : 0
% 9.28/3.61  #Close   : 0
% 9.28/3.61  
% 9.28/3.61  Ordering : KBO
% 9.28/3.61  
% 9.28/3.61  Simplification rules
% 9.28/3.61  ----------------------
% 9.28/3.61  #Subsume      : 291
% 9.28/3.61  #Demod        : 249
% 9.28/3.61  #Tautology    : 54
% 9.28/3.61  #SimpNegUnit  : 29
% 9.28/3.61  #BackRed      : 0
% 9.28/3.61  
% 9.28/3.61  #Partial instantiations: 0
% 9.28/3.61  #Strategies tried      : 1
% 9.28/3.61  
% 9.28/3.61  Timing (in seconds)
% 9.28/3.61  ----------------------
% 9.28/3.61  Preprocessing        : 0.30
% 9.28/3.61  Parsing              : 0.17
% 9.28/3.61  CNF conversion       : 0.02
% 9.28/3.61  Main loop            : 2.49
% 9.28/3.61  Inferencing          : 0.53
% 9.28/3.61  Reduction            : 0.36
% 9.28/3.61  Demodulation         : 0.23
% 9.28/3.61  BG Simplification    : 0.05
% 9.28/3.61  Subsumption          : 1.44
% 9.28/3.61  Abstraction          : 0.06
% 9.28/3.61  MUC search           : 0.00
% 9.28/3.61  Cooper               : 0.00
% 9.28/3.61  Total                : 2.83
% 9.28/3.61  Index Insertion      : 0.00
% 9.28/3.61  Index Deletion       : 0.00
% 9.28/3.61  Index Matching       : 0.00
% 9.28/3.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
