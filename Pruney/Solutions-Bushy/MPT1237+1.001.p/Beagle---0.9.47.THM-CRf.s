%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1237+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:37 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 148 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(B,C)
                 => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

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

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_8,C_11,B_9] :
      ( r1_tarski(k3_subset_1(A_8,C_11),k3_subset_1(A_8,B_9))
      | ~ r1_tarski(B_9,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k3_subset_1(u1_struct_0(A_1),k2_pre_topc(A_1,k3_subset_1(u1_struct_0(A_1),B_3))) = k1_tops_1(A_1,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_16,C_18] :
      ( r1_tarski(k2_pre_topc(A_12,B_16),k2_pre_topc(A_12,C_18))
      | ~ r1_tarski(B_16,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_31,plain,(
    ! [A_33,B_34] :
      ( k3_subset_1(u1_struct_0(A_33),k2_pre_topc(A_33,k3_subset_1(u1_struct_0(A_33),B_34))) = k1_tops_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_52,B_53,B_54] :
      ( r1_tarski(k1_tops_1(A_52,B_53),k3_subset_1(u1_struct_0(A_52),B_54))
      | ~ r1_tarski(B_54,k2_pre_topc(A_52,k3_subset_1(u1_struct_0(A_52),B_53)))
      | ~ m1_subset_1(k2_pre_topc(A_52,k3_subset_1(u1_struct_0(A_52),B_53)),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_10])).

tff(c_362,plain,(
    ! [A_88,B_89,B_90] :
      ( r1_tarski(k1_tops_1(A_88,B_89),k3_subset_1(u1_struct_0(A_88),k2_pre_topc(A_88,B_90)))
      | ~ m1_subset_1(k2_pre_topc(A_88,k3_subset_1(u1_struct_0(A_88),B_89)),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(k2_pre_topc(A_88,B_90),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ r1_tarski(B_90,k3_subset_1(u1_struct_0(A_88),B_89))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_88),B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_373,plain,(
    ! [A_91,B_92,B_93] :
      ( r1_tarski(k1_tops_1(A_91,B_92),k3_subset_1(u1_struct_0(A_91),k2_pre_topc(A_91,B_93)))
      | ~ m1_subset_1(k2_pre_topc(A_91,B_93),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ r1_tarski(B_93,k3_subset_1(u1_struct_0(A_91),B_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_91),B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_4,c_362])).

tff(c_585,plain,(
    ! [A_117,B_118,B_119] :
      ( r1_tarski(k1_tops_1(A_117,B_118),k1_tops_1(A_117,B_119))
      | ~ m1_subset_1(k2_pre_topc(A_117,k3_subset_1(u1_struct_0(A_117),B_119)),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_117),B_119),k3_subset_1(u1_struct_0(A_117),B_118))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_117),B_119),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_117),B_118),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_373])).

tff(c_596,plain,(
    ! [A_120,B_121,B_122] :
      ( r1_tarski(k1_tops_1(A_120,B_121),k1_tops_1(A_120,B_122))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_120),B_122),k3_subset_1(u1_struct_0(A_120),B_121))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_120),B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_120),B_122),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_4,c_585])).

tff(c_620,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(k1_tops_1(A_123,B_124),k1_tops_1(A_123,C_125))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_123),B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_123),C_125),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ r1_tarski(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123))) ) ),
    inference(resolution,[status(thm)],[c_10,c_596])).

tff(c_631,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k1_tops_1(A_126,B_127),k1_tops_1(A_126,C_128))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_126),C_128),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ r1_tarski(B_127,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126))) ) ),
    inference(resolution,[status(thm)],[c_6,c_620])).

tff(c_642,plain,(
    ! [A_129,B_130,B_131] :
      ( r1_tarski(k1_tops_1(A_129,B_130),k1_tops_1(A_129,B_131))
      | ~ l1_pre_topc(A_129)
      | ~ r1_tarski(B_130,B_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_129))) ) ),
    inference(resolution,[status(thm)],[c_6,c_631])).

tff(c_14,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_645,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_642,c_14])).

tff(c_655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_16,c_22,c_645])).

%------------------------------------------------------------------------------
