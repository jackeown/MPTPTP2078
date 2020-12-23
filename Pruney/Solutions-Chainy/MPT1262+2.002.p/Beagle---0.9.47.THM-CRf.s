%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:37 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 211 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 473 expanded)
%              Number of equality atoms :   24 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & r1_tarski(B,C) )
                 => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_40,plain,(
    ~ v1_tops_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_65,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_74,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46])).

tff(c_220,plain,(
    ! [B_70,A_71] :
      ( v1_tops_1(B_70,A_71)
      | k2_pre_topc(A_71,B_70) != k2_struct_0(A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_226,plain,(
    ! [B_70] :
      ( v1_tops_1(B_70,'#skF_3')
      | k2_pre_topc('#skF_3',B_70) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_220])).

tff(c_246,plain,(
    ! [B_74] :
      ( v1_tops_1(B_74,'#skF_3')
      | k2_pre_topc('#skF_3',B_74) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_226])).

tff(c_252,plain,
    ( v1_tops_1('#skF_5','#skF_3')
    | k2_pre_topc('#skF_3','#skF_5') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_246])).

tff(c_263,plain,(
    k2_pre_topc('#skF_3','#skF_5') != k2_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_252])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_75,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48])).

tff(c_44,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_268,plain,(
    ! [A_77,B_78] :
      ( k2_pre_topc(A_77,B_78) = k2_struct_0(A_77)
      | ~ v1_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_274,plain,(
    ! [B_78] :
      ( k2_pre_topc('#skF_3',B_78) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_268])).

tff(c_298,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_3',B_83) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_274])).

tff(c_307,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_298])).

tff(c_317,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_307])).

tff(c_34,plain,(
    ! [A_19,B_23,C_25] :
      ( r1_tarski(k2_pre_topc(A_19,B_23),k2_pre_topc(A_19,C_25))
      | ~ r1_tarski(B_23,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_323,plain,(
    ! [C_25] :
      ( r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',C_25))
      | ~ r1_tarski('#skF_4',C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_34])).

tff(c_339,plain,(
    ! [C_25] :
      ( r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',C_25))
      | ~ r1_tarski('#skF_4',C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_75,c_74,c_74,c_323])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_56,A_57] :
      ( r1_tarski(A_56,A_57)
      | v1_xboole_0(k1_zfmisc_1(A_57))
      | ~ m1_subset_1(A_56,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_98,c_8])).

tff(c_145,plain,
    ( r1_tarski('#skF_5',k2_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_76,c_135])).

tff(c_149,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_104,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_50,A_51] :
      ( ~ v1_xboole_0(A_50)
      | ~ r2_hidden(A_51,A_50) ) ),
    inference(resolution,[status(thm)],[c_51,c_104])).

tff(c_122,plain,(
    ! [A_3,C_7] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_153,plain,(
    ! [C_58] : ~ r1_tarski(C_58,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_149,c_122])).

tff(c_158,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_160,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_197,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k2_pre_topc(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_205,plain,(
    ! [B_68] :
      ( m1_subset_1(k2_pre_topc('#skF_3',B_68),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_197])).

tff(c_210,plain,(
    ! [B_69] :
      ( m1_subset_1(k2_pre_topc('#skF_3',B_69),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_74,c_205])).

tff(c_103,plain,(
    ! [A_45,A_3] :
      ( r1_tarski(A_45,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_98,c_8])).

tff(c_213,plain,(
    ! [B_69] :
      ( r1_tarski(k2_pre_topc('#skF_3',B_69),k2_struct_0('#skF_3'))
      | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_210,c_103])).

tff(c_235,plain,(
    ! [B_72] :
      ( r1_tarski(k2_pre_topc('#skF_3',B_72),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_213])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_400,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_3',B_96) = k2_struct_0('#skF_3')
      | ~ r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_410,plain,(
    ! [C_97] :
      ( k2_pre_topc('#skF_3',C_97) = k2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_4',C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_339,c_400])).

tff(c_416,plain,
    ( k2_pre_topc('#skF_3','#skF_5') = k2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_410])).

tff(c_427,plain,(
    k2_pre_topc('#skF_3','#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_416])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.72  
% 2.94/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.73  %$ v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.94/1.73  
% 2.94/1.73  %Foreground sorts:
% 2.94/1.73  
% 2.94/1.73  
% 2.94/1.73  %Background operators:
% 2.94/1.73  
% 2.94/1.73  
% 2.94/1.73  %Foreground operators:
% 2.94/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.73  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.73  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.94/1.73  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.73  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.94/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.94/1.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.94/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.94/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.73  
% 2.94/1.74  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 2.94/1.74  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.94/1.74  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.94/1.74  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 2.94/1.74  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 2.94/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.74  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.94/1.74  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.94/1.74  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.94/1.74  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.94/1.74  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.94/1.74  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.94/1.74  tff(c_40, plain, (~v1_tops_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.94/1.74  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.94/1.74  tff(c_32, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.94/1.74  tff(c_65, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.74  tff(c_70, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.94/1.74  tff(c_74, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_70])).
% 2.94/1.74  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.94/1.74  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46])).
% 2.94/1.74  tff(c_220, plain, (![B_70, A_71]: (v1_tops_1(B_70, A_71) | k2_pre_topc(A_71, B_70)!=k2_struct_0(A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.94/1.74  tff(c_226, plain, (![B_70]: (v1_tops_1(B_70, '#skF_3') | k2_pre_topc('#skF_3', B_70)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_220])).
% 2.94/1.74  tff(c_246, plain, (![B_74]: (v1_tops_1(B_74, '#skF_3') | k2_pre_topc('#skF_3', B_74)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_226])).
% 2.94/1.74  tff(c_252, plain, (v1_tops_1('#skF_5', '#skF_3') | k2_pre_topc('#skF_3', '#skF_5')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_246])).
% 2.94/1.74  tff(c_263, plain, (k2_pre_topc('#skF_3', '#skF_5')!=k2_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_252])).
% 2.94/1.74  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.94/1.74  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.94/1.74  tff(c_75, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48])).
% 2.94/1.74  tff(c_44, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.94/1.74  tff(c_268, plain, (![A_77, B_78]: (k2_pre_topc(A_77, B_78)=k2_struct_0(A_77) | ~v1_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.94/1.74  tff(c_274, plain, (![B_78]: (k2_pre_topc('#skF_3', B_78)=k2_struct_0('#skF_3') | ~v1_tops_1(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_268])).
% 2.94/1.74  tff(c_298, plain, (![B_83]: (k2_pre_topc('#skF_3', B_83)=k2_struct_0('#skF_3') | ~v1_tops_1(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_274])).
% 2.94/1.74  tff(c_307, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_75, c_298])).
% 2.94/1.74  tff(c_317, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_307])).
% 2.94/1.74  tff(c_34, plain, (![A_19, B_23, C_25]: (r1_tarski(k2_pre_topc(A_19, B_23), k2_pre_topc(A_19, C_25)) | ~r1_tarski(B_23, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.94/1.74  tff(c_323, plain, (![C_25]: (r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', C_25)) | ~r1_tarski('#skF_4', C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_317, c_34])).
% 2.94/1.74  tff(c_339, plain, (![C_25]: (r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', C_25)) | ~r1_tarski('#skF_4', C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_75, c_74, c_74, c_323])).
% 2.94/1.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.74  tff(c_98, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.74  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.74  tff(c_135, plain, (![A_56, A_57]: (r1_tarski(A_56, A_57) | v1_xboole_0(k1_zfmisc_1(A_57)) | ~m1_subset_1(A_56, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_98, c_8])).
% 2.94/1.74  tff(c_145, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_76, c_135])).
% 2.94/1.74  tff(c_149, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_145])).
% 2.94/1.74  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.74  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.94/1.74  tff(c_22, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.74  tff(c_51, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.94/1.74  tff(c_104, plain, (![C_47, B_48, A_49]: (~v1_xboole_0(C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.74  tff(c_114, plain, (![A_50, A_51]: (~v1_xboole_0(A_50) | ~r2_hidden(A_51, A_50))), inference(resolution, [status(thm)], [c_51, c_104])).
% 2.94/1.74  tff(c_122, plain, (![A_3, C_7]: (~v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_10, c_114])).
% 2.94/1.74  tff(c_153, plain, (![C_58]: (~r1_tarski(C_58, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_149, c_122])).
% 2.94/1.74  tff(c_158, plain, $false, inference(resolution, [status(thm)], [c_6, c_153])).
% 2.94/1.74  tff(c_160, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_145])).
% 2.94/1.74  tff(c_197, plain, (![A_67, B_68]: (m1_subset_1(k2_pre_topc(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.74  tff(c_205, plain, (![B_68]: (m1_subset_1(k2_pre_topc('#skF_3', B_68), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_197])).
% 2.94/1.74  tff(c_210, plain, (![B_69]: (m1_subset_1(k2_pre_topc('#skF_3', B_69), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_74, c_205])).
% 2.94/1.74  tff(c_103, plain, (![A_45, A_3]: (r1_tarski(A_45, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_98, c_8])).
% 2.94/1.74  tff(c_213, plain, (![B_69]: (r1_tarski(k2_pre_topc('#skF_3', B_69), k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_210, c_103])).
% 2.94/1.74  tff(c_235, plain, (![B_72]: (r1_tarski(k2_pre_topc('#skF_3', B_72), k2_struct_0('#skF_3')) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_160, c_213])).
% 2.94/1.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.74  tff(c_400, plain, (![B_96]: (k2_pre_topc('#skF_3', B_96)=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_235, c_2])).
% 2.94/1.74  tff(c_410, plain, (![C_97]: (k2_pre_topc('#skF_3', C_97)=k2_struct_0('#skF_3') | ~r1_tarski('#skF_4', C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_339, c_400])).
% 2.94/1.74  tff(c_416, plain, (k2_pre_topc('#skF_3', '#skF_5')=k2_struct_0('#skF_3') | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_410])).
% 2.94/1.74  tff(c_427, plain, (k2_pre_topc('#skF_3', '#skF_5')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_416])).
% 2.94/1.74  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_427])).
% 2.94/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.74  
% 2.94/1.74  Inference rules
% 2.94/1.74  ----------------------
% 2.94/1.74  #Ref     : 0
% 2.94/1.74  #Sup     : 78
% 2.94/1.74  #Fact    : 0
% 2.94/1.74  #Define  : 0
% 2.94/1.74  #Split   : 6
% 2.94/1.74  #Chain   : 0
% 2.94/1.74  #Close   : 0
% 2.94/1.74  
% 2.94/1.74  Ordering : KBO
% 2.94/1.74  
% 2.94/1.74  Simplification rules
% 2.94/1.74  ----------------------
% 2.94/1.74  #Subsume      : 10
% 2.94/1.74  #Demod        : 44
% 2.94/1.74  #Tautology    : 20
% 2.94/1.74  #SimpNegUnit  : 7
% 2.94/1.74  #BackRed      : 2
% 2.94/1.74  
% 2.94/1.74  #Partial instantiations: 0
% 2.94/1.74  #Strategies tried      : 1
% 2.94/1.74  
% 2.94/1.74  Timing (in seconds)
% 2.94/1.74  ----------------------
% 2.94/1.75  Preprocessing        : 0.48
% 2.94/1.75  Parsing              : 0.26
% 2.94/1.75  CNF conversion       : 0.03
% 2.94/1.75  Main loop            : 0.37
% 2.94/1.75  Inferencing          : 0.13
% 2.94/1.75  Reduction            : 0.11
% 2.94/1.75  Demodulation         : 0.08
% 2.94/1.75  BG Simplification    : 0.02
% 2.94/1.75  Subsumption          : 0.08
% 2.94/1.75  Abstraction          : 0.02
% 2.94/1.75  MUC search           : 0.00
% 2.94/1.75  Cooper               : 0.00
% 2.94/1.75  Total                : 0.89
% 2.94/1.75  Index Insertion      : 0.00
% 2.94/1.75  Index Deletion       : 0.00
% 2.94/1.75  Index Matching       : 0.00
% 2.94/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
