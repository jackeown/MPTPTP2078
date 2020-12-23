%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:51 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 904 expanded)
%              Number of leaves         :   29 ( 310 expanded)
%              Depth                    :   21
%              Number of atoms          :  200 (1965 expanded)
%              Number of equality atoms :   37 ( 279 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k2_tops_1(A,k2_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_34,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_173,plain,(
    ! [A_60,B_61] :
      ( k2_tops_1(A_60,k3_subset_1(u1_struct_0(A_60),B_61)) = k2_tops_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_182,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_188,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_182])).

tff(c_28,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_192,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_28])).

tff(c_196,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_192])).

tff(c_198,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_201,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_201])).

tff(c_206,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_30,plain,(
    ! [A_34,B_36] :
      ( k2_tops_1(A_34,k3_subset_1(u1_struct_0(A_34),B_36)) = k2_tops_1(A_34,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_226,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_30])).

tff(c_238,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_226])).

tff(c_300,plain,
    ( m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_28])).

tff(c_304,plain,
    ( m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_300])).

tff(c_2473,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_2476,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_2473])).

tff(c_2480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_2476])).

tff(c_2481,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_pre_topc(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_207,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_306,plain,(
    ! [A_63,B_64] :
      ( k4_subset_1(u1_struct_0(A_63),B_64,k2_tops_1(A_63,B_64)) = k2_pre_topc(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_319,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_306])).

tff(c_331,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_319])).

tff(c_426,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(k3_subset_1(A_70,k4_subset_1(A_70,B_71,C_72)),k3_subset_1(A_70,B_71))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_446,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_426])).

tff(c_472,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_206,c_446])).

tff(c_512,plain,(
    ! [B_74,C_75,A_76] :
      ( r1_tarski(B_74,C_75)
      | ~ r1_tarski(k3_subset_1(A_76,C_75),k3_subset_1(A_76,B_74))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_518,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_472,c_512])).

tff(c_552,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_518])).

tff(c_561,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_564,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_561])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_564])).

tff(c_570,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_49,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_574,plain,(
    ! [A_77,B_78] :
      ( k9_subset_1(u1_struct_0(A_77),k2_pre_topc(A_77,B_78),k2_pre_topc(A_77,k3_subset_1(u1_struct_0(A_77),B_78))) = k2_tops_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_599,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_574])).

tff(c_611,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_207,c_188,c_599])).

tff(c_110,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,k2_pre_topc(A_54,B_55)) = k2_pre_topc(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_119,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_110])).

tff(c_125,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_119])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k2_pre_topc(A_20,k2_pre_topc(A_20,B_21)) = k2_pre_topc(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_253,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_22])).

tff(c_263,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_253])).

tff(c_24,plain,(
    ! [A_22,B_26,C_28] :
      ( r1_tarski(k2_pre_topc(A_22,k9_subset_1(u1_struct_0(A_22),B_26,C_28)),k9_subset_1(u1_struct_0(A_22),k2_pre_topc(A_22,B_26),k2_pre_topc(A_22,C_28)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_756,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_24])).

tff(c_763,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_570,c_611,c_125,c_263,c_756])).

tff(c_1199,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_1202,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1199])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_207,c_1202])).

tff(c_1207,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1263,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1207,c_2])).

tff(c_1308,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1263])).

tff(c_1630,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_1633,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_1630])).

tff(c_1637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_1633])).

tff(c_1638,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_310,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_306])).

tff(c_325,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_310])).

tff(c_18,plain,(
    ! [A_14,B_15,C_17] :
      ( r1_tarski(k3_subset_1(A_14,k4_subset_1(A_14,B_15,C_17)),k3_subset_1(A_14,B_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1992,plain,(
    ! [B_104,A_105,C_106] :
      ( r1_tarski(B_104,k4_subset_1(A_105,B_104,C_106))
      | ~ m1_subset_1(k4_subset_1(A_105,B_104,C_106),k1_zfmisc_1(A_105))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_18,c_512])).

tff(c_2018,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_1992])).

tff(c_2052,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_1638,c_325,c_2018])).

tff(c_2053,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1308,c_2052])).

tff(c_2064,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2053])).

tff(c_2068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_206,c_2064])).

tff(c_2069,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1263])).

tff(c_2073,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_325])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( k4_subset_1(A_3,C_5,B_4) = k4_subset_1(A_3,B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [B_4] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),B_4) = k4_subset_1(u1_struct_0('#skF_1'),B_4,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_206,c_8])).

tff(c_2488,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2481,c_240])).

tff(c_2514,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2073,c_2488])).

tff(c_2623,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2514,c_18])).

tff(c_2627,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2481,c_206,c_2623])).

tff(c_14,plain,(
    ! [B_11,C_13,A_10] :
      ( r1_tarski(B_11,C_13)
      | ~ r1_tarski(k3_subset_1(A_10,C_13),k3_subset_1(A_10,B_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2631,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2627,c_14])).

tff(c_2636,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2481,c_206,c_2631])).

tff(c_2638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/2.03  
% 4.81/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/2.03  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.81/2.03  
% 4.81/2.03  %Foreground sorts:
% 4.81/2.03  
% 4.81/2.03  
% 4.81/2.03  %Background operators:
% 4.81/2.03  
% 4.81/2.03  
% 4.81/2.03  %Foreground operators:
% 4.81/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/2.03  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.81/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.81/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/2.03  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.81/2.03  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.81/2.03  tff('#skF_2', type, '#skF_2': $i).
% 4.81/2.03  tff('#skF_1', type, '#skF_1': $i).
% 4.81/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.81/2.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.81/2.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.81/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/2.03  
% 5.11/2.05  tff(f_118, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_1)).
% 5.11/2.05  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.11/2.05  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 5.11/2.05  tff(f_96, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.11/2.05  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.11/2.05  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.11/2.05  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 5.11/2.05  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 5.11/2.05  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.11/2.05  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 5.11/2.05  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 5.11/2.05  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 5.11/2.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.11/2.05  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 5.11/2.05  tff(c_34, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.11/2.05  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.11/2.05  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.11/2.05  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.11/2.05  tff(c_173, plain, (![A_60, B_61]: (k2_tops_1(A_60, k3_subset_1(u1_struct_0(A_60), B_61))=k2_tops_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/2.05  tff(c_182, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_173])).
% 5.11/2.05  tff(c_188, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_182])).
% 5.11/2.05  tff(c_28, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.11/2.05  tff(c_192, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_188, c_28])).
% 5.11/2.05  tff(c_196, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_192])).
% 5.11/2.05  tff(c_198, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_196])).
% 5.11/2.05  tff(c_201, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_198])).
% 5.11/2.05  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_201])).
% 5.11/2.05  tff(c_206, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_196])).
% 5.11/2.05  tff(c_30, plain, (![A_34, B_36]: (k2_tops_1(A_34, k3_subset_1(u1_struct_0(A_34), B_36))=k2_tops_1(A_34, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/2.05  tff(c_226, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_206, c_30])).
% 5.11/2.05  tff(c_238, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_226])).
% 5.11/2.05  tff(c_300, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_238, c_28])).
% 5.11/2.05  tff(c_304, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_300])).
% 5.11/2.05  tff(c_2473, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_304])).
% 5.11/2.05  tff(c_2476, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_2473])).
% 5.11/2.05  tff(c_2480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_2476])).
% 5.11/2.05  tff(c_2481, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_304])).
% 5.11/2.05  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(k2_pre_topc(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.11/2.05  tff(c_207, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_196])).
% 5.11/2.05  tff(c_306, plain, (![A_63, B_64]: (k4_subset_1(u1_struct_0(A_63), B_64, k2_tops_1(A_63, B_64))=k2_pre_topc(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.11/2.05  tff(c_319, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_306])).
% 5.11/2.05  tff(c_331, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_319])).
% 5.11/2.05  tff(c_426, plain, (![A_70, B_71, C_72]: (r1_tarski(k3_subset_1(A_70, k4_subset_1(A_70, B_71, C_72)), k3_subset_1(A_70, B_71)) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.11/2.05  tff(c_446, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_331, c_426])).
% 5.11/2.05  tff(c_472, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_206, c_446])).
% 5.11/2.05  tff(c_512, plain, (![B_74, C_75, A_76]: (r1_tarski(B_74, C_75) | ~r1_tarski(k3_subset_1(A_76, C_75), k3_subset_1(A_76, B_74)) | ~m1_subset_1(C_75, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.11/2.05  tff(c_518, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_472, c_512])).
% 5.11/2.05  tff(c_552, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_518])).
% 5.11/2.05  tff(c_561, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_552])).
% 5.11/2.05  tff(c_564, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_561])).
% 5.11/2.05  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_564])).
% 5.11/2.05  tff(c_570, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_552])).
% 5.11/2.05  tff(c_49, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.11/2.05  tff(c_55, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_49])).
% 5.11/2.05  tff(c_574, plain, (![A_77, B_78]: (k9_subset_1(u1_struct_0(A_77), k2_pre_topc(A_77, B_78), k2_pre_topc(A_77, k3_subset_1(u1_struct_0(A_77), B_78)))=k2_tops_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.11/2.05  tff(c_599, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_55, c_574])).
% 5.11/2.05  tff(c_611, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_207, c_188, c_599])).
% 5.11/2.05  tff(c_110, plain, (![A_54, B_55]: (k2_pre_topc(A_54, k2_pre_topc(A_54, B_55))=k2_pre_topc(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.11/2.05  tff(c_119, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_110])).
% 5.11/2.05  tff(c_125, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_119])).
% 5.11/2.05  tff(c_22, plain, (![A_20, B_21]: (k2_pre_topc(A_20, k2_pre_topc(A_20, B_21))=k2_pre_topc(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.11/2.05  tff(c_253, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_207, c_22])).
% 5.11/2.05  tff(c_263, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_253])).
% 5.11/2.05  tff(c_24, plain, (![A_22, B_26, C_28]: (r1_tarski(k2_pre_topc(A_22, k9_subset_1(u1_struct_0(A_22), B_26, C_28)), k9_subset_1(u1_struct_0(A_22), k2_pre_topc(A_22, B_26), k2_pre_topc(A_22, C_28))) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.11/2.05  tff(c_756, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_611, c_24])).
% 5.11/2.05  tff(c_763, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_570, c_611, c_125, c_263, c_756])).
% 5.11/2.05  tff(c_1199, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_763])).
% 5.11/2.05  tff(c_1202, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1199])).
% 5.11/2.05  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_207, c_1202])).
% 5.11/2.05  tff(c_1207, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_763])).
% 5.11/2.05  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.11/2.05  tff(c_1263, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1207, c_2])).
% 5.11/2.05  tff(c_1308, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1263])).
% 5.11/2.05  tff(c_1630, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_304])).
% 5.11/2.05  tff(c_1633, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_1630])).
% 5.11/2.05  tff(c_1637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_1633])).
% 5.11/2.05  tff(c_1638, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_304])).
% 5.11/2.05  tff(c_310, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_206, c_306])).
% 5.11/2.05  tff(c_325, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_310])).
% 5.11/2.05  tff(c_18, plain, (![A_14, B_15, C_17]: (r1_tarski(k3_subset_1(A_14, k4_subset_1(A_14, B_15, C_17)), k3_subset_1(A_14, B_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.11/2.05  tff(c_1992, plain, (![B_104, A_105, C_106]: (r1_tarski(B_104, k4_subset_1(A_105, B_104, C_106)) | ~m1_subset_1(k4_subset_1(A_105, B_104, C_106), k1_zfmisc_1(A_105)) | ~m1_subset_1(C_106, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_18, c_512])).
% 5.11/2.05  tff(c_2018, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_325, c_1992])).
% 5.11/2.05  tff(c_2052, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_1638, c_325, c_2018])).
% 5.11/2.05  tff(c_2053, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1308, c_2052])).
% 5.11/2.05  tff(c_2064, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_2053])).
% 5.11/2.05  tff(c_2068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_206, c_2064])).
% 5.11/2.05  tff(c_2069, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1263])).
% 5.11/2.05  tff(c_2073, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_325])).
% 5.11/2.05  tff(c_8, plain, (![A_3, C_5, B_4]: (k4_subset_1(A_3, C_5, B_4)=k4_subset_1(A_3, B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.11/2.05  tff(c_240, plain, (![B_4]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), B_4)=k4_subset_1(u1_struct_0('#skF_1'), B_4, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_206, c_8])).
% 5.11/2.05  tff(c_2488, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_2481, c_240])).
% 5.11/2.05  tff(c_2514, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2073, c_2488])).
% 5.11/2.05  tff(c_2623, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2514, c_18])).
% 5.11/2.05  tff(c_2627, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2481, c_206, c_2623])).
% 5.11/2.05  tff(c_14, plain, (![B_11, C_13, A_10]: (r1_tarski(B_11, C_13) | ~r1_tarski(k3_subset_1(A_10, C_13), k3_subset_1(A_10, B_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.11/2.05  tff(c_2631, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2627, c_14])).
% 5.11/2.05  tff(c_2636, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2481, c_206, c_2631])).
% 5.11/2.05  tff(c_2638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2636])).
% 5.11/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/2.05  
% 5.11/2.05  Inference rules
% 5.11/2.05  ----------------------
% 5.11/2.05  #Ref     : 0
% 5.11/2.05  #Sup     : 618
% 5.11/2.05  #Fact    : 0
% 5.11/2.05  #Define  : 0
% 5.11/2.05  #Split   : 8
% 5.11/2.05  #Chain   : 0
% 5.11/2.05  #Close   : 0
% 5.11/2.05  
% 5.11/2.05  Ordering : KBO
% 5.11/2.05  
% 5.11/2.05  Simplification rules
% 5.11/2.05  ----------------------
% 5.11/2.05  #Subsume      : 25
% 5.11/2.05  #Demod        : 585
% 5.11/2.05  #Tautology    : 245
% 5.11/2.05  #SimpNegUnit  : 2
% 5.11/2.05  #BackRed      : 3
% 5.11/2.05  
% 5.11/2.05  #Partial instantiations: 0
% 5.11/2.05  #Strategies tried      : 1
% 5.11/2.05  
% 5.11/2.05  Timing (in seconds)
% 5.11/2.05  ----------------------
% 5.11/2.05  Preprocessing        : 0.38
% 5.11/2.05  Parsing              : 0.17
% 5.11/2.05  CNF conversion       : 0.04
% 5.11/2.05  Main loop            : 0.81
% 5.11/2.05  Inferencing          : 0.25
% 5.11/2.05  Reduction            : 0.31
% 5.11/2.05  Demodulation         : 0.22
% 5.11/2.05  BG Simplification    : 0.04
% 5.11/2.05  Subsumption          : 0.16
% 5.11/2.05  Abstraction          : 0.04
% 5.11/2.05  MUC search           : 0.00
% 5.11/2.05  Cooper               : 0.00
% 5.11/2.05  Total                : 1.23
% 5.11/2.05  Index Insertion      : 0.00
% 5.11/2.05  Index Deletion       : 0.00
% 5.11/2.05  Index Matching       : 0.00
% 5.11/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
