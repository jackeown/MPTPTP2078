%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1312+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:46 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 135 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_129,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_76,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_210,plain,(
    ! [B_107,A_108] :
      ( l1_pre_topc(B_107)
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_213,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_210])).

tff(c_216,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_213])).

tff(c_26,plain,(
    ! [B_28,A_6] :
      ( r1_tarski(k2_struct_0(B_28),k2_struct_0(A_6))
      | ~ m1_pre_topc(B_28,A_6)
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_50] :
      ( l1_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    ! [A_95] :
      ( u1_struct_0(A_95) = k2_struct_0(A_95)
      | ~ l1_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_220,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_216,c_95])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_195,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(A_104,B_105)
      | ~ m1_subset_1(A_104,k1_zfmisc_1(B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_207,plain,(
    r1_tarski('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_74,c_195])).

tff(c_221,plain,(
    r1_tarski('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_207])).

tff(c_68,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_zfmisc_1(A_79),k1_zfmisc_1(B_80))
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_352,plain,(
    ! [A_125,C_126,B_127] :
      ( r1_tarski(A_125,C_126)
      | ~ r1_tarski(B_127,C_126)
      | ~ r1_tarski(A_125,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4923,plain,(
    ! [A_391,B_392,A_393] :
      ( r1_tarski(A_391,k1_zfmisc_1(B_392))
      | ~ r1_tarski(A_391,k1_zfmisc_1(A_393))
      | ~ r1_tarski(A_393,B_392) ) ),
    inference(resolution,[status(thm)],[c_68,c_352])).

tff(c_4973,plain,(
    ! [B_394] :
      ( r1_tarski('#skF_7',k1_zfmisc_1(B_394))
      | ~ r1_tarski(k2_struct_0('#skF_6'),B_394) ) ),
    inference(resolution,[status(thm)],[c_221,c_4923])).

tff(c_4993,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_7',k1_zfmisc_1(k2_struct_0(A_6)))
      | ~ m1_pre_topc('#skF_6',A_6)
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_26,c_4973])).

tff(c_5144,plain,(
    ! [A_400] :
      ( r1_tarski('#skF_7',k1_zfmisc_1(k2_struct_0(A_400)))
      | ~ m1_pre_topc('#skF_6',A_400)
      | ~ l1_pre_topc(A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_4993])).

tff(c_190,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(A_102,k1_zfmisc_1(B_103))
      | ~ r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_180,plain,(
    ! [A_101] :
      ( u1_struct_0(A_101) = k2_struct_0(A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_184,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_180])).

tff(c_72,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_185,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_72])).

tff(c_194,plain,(
    ~ r1_tarski('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_190,c_185])).

tff(c_5157,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_5144,c_194])).

tff(c_5168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5157])).

%------------------------------------------------------------------------------
