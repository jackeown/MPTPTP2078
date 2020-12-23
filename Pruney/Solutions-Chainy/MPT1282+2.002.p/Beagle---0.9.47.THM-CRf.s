%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:20 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 198 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 513 expanded)
%              Number of equality atoms :   29 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v6_tops_1(B,A)
             => ( k2_tops_1(A,B) = k2_tops_1(A,k2_pre_topc(A,B))
                & k2_tops_1(A,k2_pre_topc(A,B)) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k1_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_tops_1(A_16,k2_pre_topc(A_16,B_18)),k2_tops_1(A_16,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57,plain,(
    ! [A_27,B_28] :
      ( k1_tops_1(A_27,k2_pre_topc(A_27,B_28)) = B_28
      | ~ v6_tops_1(B_28,A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_65,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_61])).

tff(c_39,plain,(
    ! [A_25,B_26] :
      ( k2_pre_topc(A_25,k2_pre_topc(A_25,B_26)) = k2_pre_topc(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_47,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_43])).

tff(c_71,plain,(
    ! [B_29,A_30] :
      ( v6_tops_1(B_29,A_30)
      | k1_tops_1(A_30,k2_pre_topc(A_30,B_29)) != B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_71])).

tff(c_80,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_65,c_75])).

tff(c_118,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_121,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_121])).

tff(c_127,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_90,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k2_tops_1(A_33,k1_tops_1(A_33,B_34)),k2_tops_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_90])).

tff(c_98,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_95])).

tff(c_139,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_98])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,
    ( k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_144,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_141])).

tff(c_149,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_144])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_149])).

tff(c_155,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_154,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_164,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_154])).

tff(c_165,plain,(
    ! [B_37,A_38] :
      ( v6_tops_1(B_37,A_38)
      | k1_tops_1(A_38,k2_pre_topc(A_38,B_37)) != B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_169,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_165])).

tff(c_174,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_65,c_169])).

tff(c_194,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_197,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_197])).

tff(c_203,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_230,plain,(
    ! [A_43,B_44] :
      ( k7_subset_1(u1_struct_0(A_43),k2_pre_topc(A_43,B_44),k1_tops_1(A_43,B_44)) = k2_tops_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_239,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_230])).

tff(c_246,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_203,c_47,c_155,c_239])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  %$ v6_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.13/1.25  
% 2.13/1.25  %Foreground sorts:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Background operators:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Foreground operators:
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.25  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.13/1.25  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.13/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.13/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.13/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.13/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.25  
% 2.13/1.27  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) => ((k2_tops_1(A, B) = k2_tops_1(A, k2_pre_topc(A, B))) & (k2_tops_1(A, k2_pre_topc(A, B)) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tops_1)).
% 2.13/1.27  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 2.13/1.27  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.13/1.27  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 2.13/1.27  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.13/1.27  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k1_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_tops_1)).
% 2.13/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.27  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.13/1.27  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_20, plain, (![A_16, B_18]: (r1_tarski(k2_tops_1(A_16, k2_pre_topc(A_16, B_18)), k2_tops_1(A_16, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.27  tff(c_22, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_66, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.13/1.27  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.27  tff(c_24, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_57, plain, (![A_27, B_28]: (k1_tops_1(A_27, k2_pre_topc(A_27, B_28))=B_28 | ~v6_tops_1(B_28, A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.27  tff(c_61, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.13/1.27  tff(c_65, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_61])).
% 2.13/1.27  tff(c_39, plain, (![A_25, B_26]: (k2_pre_topc(A_25, k2_pre_topc(A_25, B_26))=k2_pre_topc(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.27  tff(c_43, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_39])).
% 2.13/1.27  tff(c_47, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_43])).
% 2.13/1.27  tff(c_71, plain, (![B_29, A_30]: (v6_tops_1(B_29, A_30) | k1_tops_1(A_30, k2_pre_topc(A_30, B_29))!=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.27  tff(c_75, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47, c_71])).
% 2.13/1.27  tff(c_80, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_65, c_75])).
% 2.13/1.27  tff(c_118, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_80])).
% 2.13/1.27  tff(c_121, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_118])).
% 2.13/1.27  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_121])).
% 2.13/1.27  tff(c_127, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_80])).
% 2.13/1.27  tff(c_90, plain, (![A_33, B_34]: (r1_tarski(k2_tops_1(A_33, k1_tops_1(A_33, B_34)), k2_tops_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.27  tff(c_95, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_90])).
% 2.13/1.27  tff(c_98, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_95])).
% 2.13/1.27  tff(c_139, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_98])).
% 2.13/1.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.27  tff(c_141, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_139, c_2])).
% 2.13/1.27  tff(c_144, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_141])).
% 2.13/1.27  tff(c_149, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_144])).
% 2.13/1.27  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_149])).
% 2.13/1.27  tff(c_155, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.13/1.27  tff(c_154, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_22])).
% 2.13/1.27  tff(c_164, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_154])).
% 2.13/1.27  tff(c_165, plain, (![B_37, A_38]: (v6_tops_1(B_37, A_38) | k1_tops_1(A_38, k2_pre_topc(A_38, B_37))!=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.27  tff(c_169, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47, c_165])).
% 2.13/1.27  tff(c_174, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_65, c_169])).
% 2.13/1.27  tff(c_194, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_174])).
% 2.13/1.27  tff(c_197, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_194])).
% 2.13/1.27  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_197])).
% 2.13/1.27  tff(c_203, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_174])).
% 2.13/1.27  tff(c_230, plain, (![A_43, B_44]: (k7_subset_1(u1_struct_0(A_43), k2_pre_topc(A_43, B_44), k1_tops_1(A_43, B_44))=k2_tops_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.27  tff(c_239, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_230])).
% 2.13/1.27  tff(c_246, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_203, c_47, c_155, c_239])).
% 2.13/1.27  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_246])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 45
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 5
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 0
% 2.13/1.27  #Demod        : 62
% 2.13/1.27  #Tautology    : 25
% 2.13/1.27  #SimpNegUnit  : 4
% 2.13/1.27  #BackRed      : 0
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.28
% 2.13/1.27  Parsing              : 0.16
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.19
% 2.13/1.27  Inferencing          : 0.07
% 2.13/1.27  Reduction            : 0.06
% 2.13/1.27  Demodulation         : 0.05
% 2.13/1.27  BG Simplification    : 0.01
% 2.13/1.27  Subsumption          : 0.04
% 2.13/1.27  Abstraction          : 0.01
% 2.13/1.27  MUC search           : 0.00
% 2.13/1.27  Cooper               : 0.00
% 2.13/1.27  Total                : 0.51
% 2.13/1.27  Index Insertion      : 0.00
% 2.13/1.27  Index Deletion       : 0.00
% 2.13/1.27  Index Matching       : 0.00
% 2.13/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
