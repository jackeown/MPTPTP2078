%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:21 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 225 expanded)
%              Number of leaves         :   25 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 616 expanded)
%              Number of equality atoms :   29 (  62 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_34,plain,
    ( ~ v6_tops_1('#skF_2','#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_43,plain,(
    ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( k2_pre_topc(A_30,B_31) = B_31
      | ~ v4_pre_topc(B_31,A_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_62])).

tff(c_68,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_65])).

tff(c_52,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(B_28,k2_pre_topc(A_29,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_57,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_61,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_69,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_61])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_74,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_40,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_40])).

tff(c_108,plain,(
    ! [A_40,B_41] :
      ( k1_tops_1(A_40,k2_pre_topc(A_40,B_41)) = B_41
      | ~ v6_tops_1(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_116,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_74,c_112])).

tff(c_14,plain,(
    ! [B_11,A_9] :
      ( v5_tops_1(B_11,A_9)
      | k2_pre_topc(A_9,k1_tops_1(A_9,B_11)) != B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_14])).

tff(c_126,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_74,c_119])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_126])).

tff(c_129,plain,(
    ~ v6_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_150,plain,(
    ! [A_46,B_47] :
      ( k2_pre_topc(A_46,B_47) = B_47
      | ~ v4_pre_topc(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_156,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_153])).

tff(c_140,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(B_44,k2_pre_topc(A_45,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_142,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_140])).

tff(c_145,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_142])).

tff(c_148,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_149,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_157,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_149])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_157])).

tff(c_162,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_208,plain,(
    ! [B_56,A_57] :
      ( v6_tops_1(B_56,A_57)
      | k1_tops_1(A_57,k2_pre_topc(A_57,B_56)) != B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_212,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_208])).

tff(c_217,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_212])).

tff(c_218,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_217])).

tff(c_130,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_186,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,k1_tops_1(A_52,B_53)) = B_53
      | ~ v5_tops_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_190,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_194,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130,c_190])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_210,plain,
    ( v6_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_208])).

tff(c_215,plain,
    ( v6_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_210])).

tff(c_219,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_222,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_222])).

tff(c_228,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( r1_tarski(B_5,k2_pre_topc(A_3,B_5))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_251,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_228,c_8])).

tff(c_267,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_194,c_251])).

tff(c_269,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_267,c_2])).

tff(c_272,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_269])).

tff(c_28,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_290,plain,(
    ! [B_66,A_67,C_68] :
      ( r1_tarski(B_66,k1_tops_1(A_67,C_68))
      | ~ r1_tarski(B_66,C_68)
      | ~ v3_pre_topc(B_66,A_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_296,plain,(
    ! [B_66] :
      ( r1_tarski(B_66,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_66,'#skF_2')
      | ~ v3_pre_topc(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_290])).

tff(c_304,plain,(
    ! [B_69] :
      ( r1_tarski(B_69,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_69,'#skF_2')
      | ~ v3_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_296])).

tff(c_314,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_304])).

tff(c_323,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_314])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.16/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.16/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.16/1.30  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.16/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.16/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.30  
% 2.16/1.31  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tops_1)).
% 2.16/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.31  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.16/1.31  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.16/1.31  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 2.16/1.31  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.16/1.31  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.16/1.31  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.16/1.31  tff(c_34, plain, (~v6_tops_1('#skF_2', '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.16/1.32  tff(c_43, plain, (~v5_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.16/1.32  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.16/1.32  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.16/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.32  tff(c_26, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.16/1.32  tff(c_62, plain, (![A_30, B_31]: (k2_pre_topc(A_30, B_31)=B_31 | ~v4_pre_topc(B_31, A_30) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.32  tff(c_65, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_62])).
% 2.16/1.32  tff(c_68, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_65])).
% 2.16/1.32  tff(c_52, plain, (![B_28, A_29]: (r1_tarski(B_28, k2_pre_topc(A_29, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.32  tff(c_54, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_52])).
% 2.16/1.32  tff(c_57, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_54])).
% 2.16/1.32  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.32  tff(c_60, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_57, c_2])).
% 2.16/1.32  tff(c_61, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 2.16/1.32  tff(c_69, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_61])).
% 2.16/1.32  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 2.16/1.32  tff(c_74, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 2.16/1.32  tff(c_40, plain, (v5_tops_1('#skF_2', '#skF_1') | v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.16/1.32  tff(c_44, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_43, c_40])).
% 2.16/1.32  tff(c_108, plain, (![A_40, B_41]: (k1_tops_1(A_40, k2_pre_topc(A_40, B_41))=B_41 | ~v6_tops_1(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.32  tff(c_112, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_108])).
% 2.16/1.32  tff(c_116, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_74, c_112])).
% 2.16/1.32  tff(c_14, plain, (![B_11, A_9]: (v5_tops_1(B_11, A_9) | k2_pre_topc(A_9, k1_tops_1(A_9, B_11))!=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.32  tff(c_119, plain, (v5_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_116, c_14])).
% 2.16/1.32  tff(c_126, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_74, c_119])).
% 2.16/1.32  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_126])).
% 2.16/1.32  tff(c_129, plain, (~v6_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.16/1.32  tff(c_150, plain, (![A_46, B_47]: (k2_pre_topc(A_46, B_47)=B_47 | ~v4_pre_topc(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.32  tff(c_153, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_150])).
% 2.16/1.32  tff(c_156, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_153])).
% 2.16/1.32  tff(c_140, plain, (![B_44, A_45]: (r1_tarski(B_44, k2_pre_topc(A_45, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.32  tff(c_142, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_140])).
% 2.16/1.32  tff(c_145, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_142])).
% 2.16/1.32  tff(c_148, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_145, c_2])).
% 2.16/1.32  tff(c_149, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_148])).
% 2.16/1.32  tff(c_157, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_149])).
% 2.16/1.32  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_157])).
% 2.16/1.32  tff(c_162, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_148])).
% 2.16/1.32  tff(c_208, plain, (![B_56, A_57]: (v6_tops_1(B_56, A_57) | k1_tops_1(A_57, k2_pre_topc(A_57, B_56))!=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.32  tff(c_212, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_162, c_208])).
% 2.16/1.32  tff(c_217, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_212])).
% 2.16/1.32  tff(c_218, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_129, c_217])).
% 2.16/1.32  tff(c_130, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.16/1.32  tff(c_186, plain, (![A_52, B_53]: (k2_pre_topc(A_52, k1_tops_1(A_52, B_53))=B_53 | ~v5_tops_1(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.32  tff(c_190, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_186])).
% 2.16/1.32  tff(c_194, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130, c_190])).
% 2.16/1.32  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.32  tff(c_210, plain, (v6_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_194, c_208])).
% 2.16/1.32  tff(c_215, plain, (v6_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_210])).
% 2.16/1.32  tff(c_219, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_215])).
% 2.16/1.32  tff(c_222, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_219])).
% 2.16/1.32  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_222])).
% 2.16/1.32  tff(c_228, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_215])).
% 2.16/1.32  tff(c_8, plain, (![B_5, A_3]: (r1_tarski(B_5, k2_pre_topc(A_3, B_5)) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.32  tff(c_251, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_228, c_8])).
% 2.16/1.32  tff(c_267, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_194, c_251])).
% 2.16/1.32  tff(c_269, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_267, c_2])).
% 2.16/1.32  tff(c_272, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_218, c_269])).
% 2.16/1.32  tff(c_28, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.16/1.32  tff(c_290, plain, (![B_66, A_67, C_68]: (r1_tarski(B_66, k1_tops_1(A_67, C_68)) | ~r1_tarski(B_66, C_68) | ~v3_pre_topc(B_66, A_67) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.32  tff(c_296, plain, (![B_66]: (r1_tarski(B_66, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_66, '#skF_2') | ~v3_pre_topc(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_290])).
% 2.16/1.32  tff(c_304, plain, (![B_69]: (r1_tarski(B_69, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_69, '#skF_2') | ~v3_pre_topc(B_69, '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_296])).
% 2.16/1.32  tff(c_314, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_304])).
% 2.16/1.32  tff(c_323, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_314])).
% 2.16/1.32  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_323])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 52
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 5
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 3
% 2.16/1.32  #Demod        : 72
% 2.16/1.32  #Tautology    : 24
% 2.16/1.32  #SimpNegUnit  : 7
% 2.16/1.32  #BackRed      : 6
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.32  Preprocessing        : 0.31
% 2.16/1.32  Parsing              : 0.17
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.23
% 2.16/1.32  Inferencing          : 0.08
% 2.16/1.32  Reduction            : 0.07
% 2.16/1.32  Demodulation         : 0.05
% 2.16/1.32  BG Simplification    : 0.02
% 2.16/1.32  Subsumption          : 0.04
% 2.16/1.32  Abstraction          : 0.01
% 2.16/1.32  MUC search           : 0.00
% 2.16/1.32  Cooper               : 0.00
% 2.16/1.32  Total                : 0.59
% 2.16/1.32  Index Insertion      : 0.00
% 2.16/1.32  Index Deletion       : 0.00
% 2.16/1.32  Index Matching       : 0.00
% 2.16/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
