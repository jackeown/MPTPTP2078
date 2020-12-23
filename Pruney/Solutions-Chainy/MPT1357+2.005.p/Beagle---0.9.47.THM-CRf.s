%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:53 EST 2020

% Result     : Theorem 14.87s
% Output     : CNFRefutation 15.07s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 927 expanded)
%              Number of leaves         :   32 ( 328 expanded)
%              Depth                    :   16
%              Number of atoms          :  207 (2590 expanded)
%              Number of equality atoms :   30 ( 598 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( B = k1_xboole_0
               => ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) )
              & ( v2_pre_topc(A)
               => ( B = k1_xboole_0
                  | ( v2_compts_1(B,A)
                  <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_16,c_112])).

tff(c_121,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_117])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22637,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_36])).

tff(c_22688,plain,(
    ! [A_415,B_416] :
      ( m1_pre_topc(k1_pre_topc(A_415,B_416),A_415)
      | ~ m1_subset_1(B_416,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ l1_pre_topc(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22693,plain,(
    ! [B_416] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_416),'#skF_2')
      | ~ m1_subset_1(B_416,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_22688])).

tff(c_22929,plain,(
    ! [B_428] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_428),'#skF_2')
      | ~ m1_subset_1(B_428,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22693])).

tff(c_22942,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22637,c_22929])).

tff(c_42,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_122,plain,(
    ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_123,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_36])).

tff(c_189,plain,(
    ! [A_64,B_65] :
      ( m1_pre_topc(k1_pre_topc(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    ! [B_65] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_65),'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_189])).

tff(c_218,plain,(
    ! [B_67] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_67),'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_194])).

tff(c_231,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_218])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_130,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_99,c_130])).

tff(c_270,plain,(
    ! [A_70,B_71] :
      ( u1_struct_0(k1_pre_topc(A_70,B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_277,plain,(
    ! [B_71] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_270])).

tff(c_399,plain,(
    ! [B_73] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_73)) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_277])).

tff(c_412,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_399])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( l1_pre_topc(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_240,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_231,c_18])).

tff(c_243,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_240])).

tff(c_116,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_112])).

tff(c_247,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_243,c_116])).

tff(c_415,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_247])).

tff(c_78,plain,
    ( v2_compts_1('#skF_3','#skF_2')
    | v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_144,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_78])).

tff(c_26,plain,(
    ! [A_22] :
      ( v2_compts_1(k2_struct_0(A_22),A_22)
      | ~ v1_compts_1(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_457,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_26])).

tff(c_464,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_144,c_457])).

tff(c_609,plain,(
    ! [A_81,B_82,C_83] :
      ( '#skF_1'(A_81,B_82,C_83) = C_83
      | v2_compts_1(C_83,A_81)
      | ~ r1_tarski(C_83,k2_struct_0(B_82))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_17526,plain,(
    ! [A_325,B_326] :
      ( '#skF_1'(A_325,B_326,k2_struct_0(B_326)) = k2_struct_0(B_326)
      | v2_compts_1(k2_struct_0(B_326),A_325)
      | ~ m1_subset_1(k2_struct_0(B_326),k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_pre_topc(B_326,A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(resolution,[status(thm)],[c_142,c_609])).

tff(c_17633,plain,(
    ! [B_326] :
      ( '#skF_1'('#skF_2',B_326,k2_struct_0(B_326)) = k2_struct_0(B_326)
      | v2_compts_1(k2_struct_0(B_326),'#skF_2')
      | ~ m1_subset_1(k2_struct_0(B_326),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_326,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_17526])).

tff(c_22516,plain,(
    ! [B_402] :
      ( '#skF_1'('#skF_2',B_402,k2_struct_0(B_402)) = k2_struct_0(B_402)
      | v2_compts_1(k2_struct_0(B_402),'#skF_2')
      | ~ m1_subset_1(k2_struct_0(B_402),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_402,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_17633])).

tff(c_22549,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_22516])).

tff(c_22586,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3'
    | v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_123,c_415,c_415,c_415,c_22549])).

tff(c_22587,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_22586])).

tff(c_30,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ v2_compts_1('#skF_1'(A_23,B_35,C_41),B_35)
      | v2_compts_1(C_41,A_23)
      | ~ r1_tarski(C_41,k2_struct_0(B_35))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_pre_topc(B_35,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22610,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22587,c_30])).

tff(c_22632,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_231,c_123,c_121,c_142,c_415,c_464,c_22610])).

tff(c_22634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_22632])).

tff(c_22636,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22635,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22947,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22942,c_18])).

tff(c_22950,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22947])).

tff(c_22770,plain,(
    ! [A_423,B_424] :
      ( u1_struct_0(k1_pre_topc(A_423,B_424)) = B_424
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ l1_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22777,plain,(
    ! [B_424] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_424)) = B_424
      | ~ m1_subset_1(B_424,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_22770])).

tff(c_22873,plain,(
    ! [B_426] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_426)) = B_426
      | ~ m1_subset_1(B_426,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22777])).

tff(c_22886,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22637,c_22873])).

tff(c_22970,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22950,c_116])).

tff(c_22972,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22886,c_22970])).

tff(c_24,plain,(
    ! [A_22] :
      ( v1_compts_1(A_22)
      | ~ v2_compts_1(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22976,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22972,c_24])).

tff(c_22983,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22950,c_22976])).

tff(c_22984,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22635,c_22983])).

tff(c_22645,plain,(
    ! [A_405,B_406] :
      ( r1_tarski(A_405,B_406)
      | ~ m1_subset_1(A_405,k1_zfmisc_1(B_406)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22657,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_99,c_22645])).

tff(c_23897,plain,(
    ! [D_473,B_474,A_475] :
      ( v2_compts_1(D_473,B_474)
      | ~ m1_subset_1(D_473,k1_zfmisc_1(u1_struct_0(B_474)))
      | ~ v2_compts_1(D_473,A_475)
      | ~ r1_tarski(D_473,k2_struct_0(B_474))
      | ~ m1_subset_1(D_473,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ m1_pre_topc(B_474,A_475)
      | ~ l1_pre_topc(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24444,plain,(
    ! [B_492,A_493] :
      ( v2_compts_1(u1_struct_0(B_492),B_492)
      | ~ v2_compts_1(u1_struct_0(B_492),A_493)
      | ~ r1_tarski(u1_struct_0(B_492),k2_struct_0(B_492))
      | ~ m1_subset_1(u1_struct_0(B_492),k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ m1_pre_topc(B_492,A_493)
      | ~ l1_pre_topc(A_493) ) ),
    inference(resolution,[status(thm)],[c_99,c_23897])).

tff(c_24469,plain,(
    ! [A_493] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_pre_topc('#skF_2','#skF_3'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),A_493)
      | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_493)
      | ~ l1_pre_topc(A_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22886,c_24444])).

tff(c_24490,plain,(
    ! [A_493] :
      ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v2_compts_1('#skF_3',A_493)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_493)
      | ~ l1_pre_topc(A_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22886,c_22657,c_22972,c_22886,c_22886,c_24469])).

tff(c_34366,plain,(
    ! [A_620] :
      ( ~ v2_compts_1('#skF_3',A_620)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_620)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_620)
      | ~ l1_pre_topc(A_620) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22984,c_24490])).

tff(c_34451,plain,
    ( ~ v2_compts_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_34366])).

tff(c_34477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22942,c_22637,c_22636,c_34451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:55:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.87/6.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.87/6.45  
% 14.87/6.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.87/6.45  %$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 14.87/6.45  
% 14.87/6.45  %Foreground sorts:
% 14.87/6.45  
% 14.87/6.45  
% 14.87/6.45  %Background operators:
% 14.87/6.45  
% 14.87/6.45  
% 14.87/6.45  %Foreground operators:
% 14.87/6.45  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 14.87/6.45  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 14.87/6.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.87/6.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.87/6.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.87/6.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.87/6.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.87/6.45  tff('#skF_2', type, '#skF_2': $i).
% 14.87/6.45  tff('#skF_3', type, '#skF_3': $i).
% 14.87/6.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 14.87/6.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.87/6.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.87/6.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.87/6.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.87/6.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.87/6.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.87/6.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.87/6.45  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 14.87/6.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.87/6.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.87/6.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.87/6.45  
% 15.07/6.48  tff(f_118, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 15.07/6.48  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.07/6.48  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 15.07/6.48  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 15.07/6.48  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 15.07/6.48  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 15.07/6.48  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 15.07/6.48  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 15.07/6.48  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 15.07/6.48  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_compts_1)).
% 15.07/6.48  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 15.07/6.48  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 15.07/6.48  tff(c_16, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.07/6.48  tff(c_112, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.07/6.48  tff(c_117, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_16, c_112])).
% 15.07/6.48  tff(c_121, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_117])).
% 15.07/6.48  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 15.07/6.48  tff(c_22637, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_36])).
% 15.07/6.48  tff(c_22688, plain, (![A_415, B_416]: (m1_pre_topc(k1_pre_topc(A_415, B_416), A_415) | ~m1_subset_1(B_416, k1_zfmisc_1(u1_struct_0(A_415))) | ~l1_pre_topc(A_415))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.07/6.48  tff(c_22693, plain, (![B_416]: (m1_pre_topc(k1_pre_topc('#skF_2', B_416), '#skF_2') | ~m1_subset_1(B_416, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_22688])).
% 15.07/6.48  tff(c_22929, plain, (![B_428]: (m1_pre_topc(k1_pre_topc('#skF_2', B_428), '#skF_2') | ~m1_subset_1(B_428, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22693])).
% 15.07/6.48  tff(c_22942, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_22637, c_22929])).
% 15.07/6.48  tff(c_42, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 15.07/6.48  tff(c_122, plain, (~v2_compts_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 15.07/6.48  tff(c_123, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_36])).
% 15.07/6.48  tff(c_189, plain, (![A_64, B_65]: (m1_pre_topc(k1_pre_topc(A_64, B_65), A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.07/6.48  tff(c_194, plain, (![B_65]: (m1_pre_topc(k1_pre_topc('#skF_2', B_65), '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_189])).
% 15.07/6.48  tff(c_218, plain, (![B_67]: (m1_pre_topc(k1_pre_topc('#skF_2', B_67), '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_194])).
% 15.07/6.48  tff(c_231, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_123, c_218])).
% 15.07/6.48  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.07/6.48  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.07/6.48  tff(c_99, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 15.07/6.48  tff(c_130, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.07/6.48  tff(c_142, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_99, c_130])).
% 15.07/6.48  tff(c_270, plain, (![A_70, B_71]: (u1_struct_0(k1_pre_topc(A_70, B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.07/6.48  tff(c_277, plain, (![B_71]: (u1_struct_0(k1_pre_topc('#skF_2', B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_270])).
% 15.07/6.48  tff(c_399, plain, (![B_73]: (u1_struct_0(k1_pre_topc('#skF_2', B_73))=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_277])).
% 15.07/6.48  tff(c_412, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_123, c_399])).
% 15.07/6.48  tff(c_18, plain, (![B_11, A_9]: (l1_pre_topc(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.07/6.48  tff(c_240, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_231, c_18])).
% 15.07/6.48  tff(c_243, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_240])).
% 15.07/6.48  tff(c_116, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_16, c_112])).
% 15.07/6.48  tff(c_247, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_243, c_116])).
% 15.07/6.48  tff(c_415, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_247])).
% 15.07/6.48  tff(c_78, plain, (v2_compts_1('#skF_3', '#skF_2') | v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 15.07/6.48  tff(c_144, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_122, c_78])).
% 15.07/6.48  tff(c_26, plain, (![A_22]: (v2_compts_1(k2_struct_0(A_22), A_22) | ~v1_compts_1(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.07/6.48  tff(c_457, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_26])).
% 15.07/6.48  tff(c_464, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_144, c_457])).
% 15.07/6.48  tff(c_609, plain, (![A_81, B_82, C_83]: ('#skF_1'(A_81, B_82, C_83)=C_83 | v2_compts_1(C_83, A_81) | ~r1_tarski(C_83, k2_struct_0(B_82)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_pre_topc(B_82, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.07/6.48  tff(c_17526, plain, (![A_325, B_326]: ('#skF_1'(A_325, B_326, k2_struct_0(B_326))=k2_struct_0(B_326) | v2_compts_1(k2_struct_0(B_326), A_325) | ~m1_subset_1(k2_struct_0(B_326), k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_pre_topc(B_326, A_325) | ~l1_pre_topc(A_325))), inference(resolution, [status(thm)], [c_142, c_609])).
% 15.07/6.48  tff(c_17633, plain, (![B_326]: ('#skF_1'('#skF_2', B_326, k2_struct_0(B_326))=k2_struct_0(B_326) | v2_compts_1(k2_struct_0(B_326), '#skF_2') | ~m1_subset_1(k2_struct_0(B_326), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_326, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_17526])).
% 15.07/6.48  tff(c_22516, plain, (![B_402]: ('#skF_1'('#skF_2', B_402, k2_struct_0(B_402))=k2_struct_0(B_402) | v2_compts_1(k2_struct_0(B_402), '#skF_2') | ~m1_subset_1(k2_struct_0(B_402), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_402, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_17633])).
% 15.07/6.48  tff(c_22549, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_415, c_22516])).
% 15.07/6.48  tff(c_22586, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3' | v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_123, c_415, c_415, c_415, c_22549])).
% 15.07/6.48  tff(c_22587, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_122, c_22586])).
% 15.07/6.48  tff(c_30, plain, (![A_23, B_35, C_41]: (~v2_compts_1('#skF_1'(A_23, B_35, C_41), B_35) | v2_compts_1(C_41, A_23) | ~r1_tarski(C_41, k2_struct_0(B_35)) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_pre_topc(B_35, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.07/6.48  tff(c_22610, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22587, c_30])).
% 15.07/6.48  tff(c_22632, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_231, c_123, c_121, c_142, c_415, c_464, c_22610])).
% 15.07/6.48  tff(c_22634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_22632])).
% 15.07/6.48  tff(c_22636, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 15.07/6.48  tff(c_22635, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 15.07/6.48  tff(c_22947, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22942, c_18])).
% 15.07/6.48  tff(c_22950, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22947])).
% 15.07/6.48  tff(c_22770, plain, (![A_423, B_424]: (u1_struct_0(k1_pre_topc(A_423, B_424))=B_424 | ~m1_subset_1(B_424, k1_zfmisc_1(u1_struct_0(A_423))) | ~l1_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.07/6.48  tff(c_22777, plain, (![B_424]: (u1_struct_0(k1_pre_topc('#skF_2', B_424))=B_424 | ~m1_subset_1(B_424, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_22770])).
% 15.07/6.48  tff(c_22873, plain, (![B_426]: (u1_struct_0(k1_pre_topc('#skF_2', B_426))=B_426 | ~m1_subset_1(B_426, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22777])).
% 15.07/6.48  tff(c_22886, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22637, c_22873])).
% 15.07/6.48  tff(c_22970, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22950, c_116])).
% 15.07/6.48  tff(c_22972, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22886, c_22970])).
% 15.07/6.48  tff(c_24, plain, (![A_22]: (v1_compts_1(A_22) | ~v2_compts_1(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.07/6.48  tff(c_22976, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22972, c_24])).
% 15.07/6.48  tff(c_22983, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22950, c_22976])).
% 15.07/6.48  tff(c_22984, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_22635, c_22983])).
% 15.07/6.48  tff(c_22645, plain, (![A_405, B_406]: (r1_tarski(A_405, B_406) | ~m1_subset_1(A_405, k1_zfmisc_1(B_406)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.07/6.48  tff(c_22657, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_99, c_22645])).
% 15.07/6.48  tff(c_23897, plain, (![D_473, B_474, A_475]: (v2_compts_1(D_473, B_474) | ~m1_subset_1(D_473, k1_zfmisc_1(u1_struct_0(B_474))) | ~v2_compts_1(D_473, A_475) | ~r1_tarski(D_473, k2_struct_0(B_474)) | ~m1_subset_1(D_473, k1_zfmisc_1(u1_struct_0(A_475))) | ~m1_pre_topc(B_474, A_475) | ~l1_pre_topc(A_475))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.07/6.48  tff(c_24444, plain, (![B_492, A_493]: (v2_compts_1(u1_struct_0(B_492), B_492) | ~v2_compts_1(u1_struct_0(B_492), A_493) | ~r1_tarski(u1_struct_0(B_492), k2_struct_0(B_492)) | ~m1_subset_1(u1_struct_0(B_492), k1_zfmisc_1(u1_struct_0(A_493))) | ~m1_pre_topc(B_492, A_493) | ~l1_pre_topc(A_493))), inference(resolution, [status(thm)], [c_99, c_23897])).
% 15.07/6.48  tff(c_24469, plain, (![A_493]: (v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), A_493) | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0(A_493))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_493) | ~l1_pre_topc(A_493))), inference(superposition, [status(thm), theory('equality')], [c_22886, c_24444])).
% 15.07/6.48  tff(c_24490, plain, (![A_493]: (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', A_493) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_493))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_493) | ~l1_pre_topc(A_493))), inference(demodulation, [status(thm), theory('equality')], [c_22886, c_22657, c_22972, c_22886, c_22886, c_24469])).
% 15.07/6.48  tff(c_34366, plain, (![A_620]: (~v2_compts_1('#skF_3', A_620) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_620))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_620) | ~l1_pre_topc(A_620))), inference(negUnitSimplification, [status(thm)], [c_22984, c_24490])).
% 15.07/6.48  tff(c_34451, plain, (~v2_compts_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121, c_34366])).
% 15.07/6.48  tff(c_34477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_22942, c_22637, c_22636, c_34451])).
% 15.07/6.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.07/6.48  
% 15.07/6.48  Inference rules
% 15.07/6.48  ----------------------
% 15.07/6.48  #Ref     : 0
% 15.07/6.48  #Sup     : 8972
% 15.07/6.48  #Fact    : 0
% 15.07/6.48  #Define  : 0
% 15.07/6.48  #Split   : 21
% 15.07/6.48  #Chain   : 0
% 15.07/6.48  #Close   : 0
% 15.07/6.48  
% 15.07/6.48  Ordering : KBO
% 15.07/6.48  
% 15.07/6.48  Simplification rules
% 15.07/6.48  ----------------------
% 15.07/6.48  #Subsume      : 1283
% 15.07/6.48  #Demod        : 7371
% 15.07/6.48  #Tautology    : 1840
% 15.07/6.48  #SimpNegUnit  : 36
% 15.07/6.48  #BackRed      : 3
% 15.07/6.48  
% 15.07/6.48  #Partial instantiations: 0
% 15.07/6.48  #Strategies tried      : 1
% 15.07/6.48  
% 15.07/6.48  Timing (in seconds)
% 15.07/6.48  ----------------------
% 15.07/6.48  Preprocessing        : 0.34
% 15.07/6.48  Parsing              : 0.17
% 15.07/6.48  CNF conversion       : 0.02
% 15.07/6.48  Main loop            : 5.36
% 15.07/6.48  Inferencing          : 1.08
% 15.07/6.48  Reduction            : 1.79
% 15.07/6.48  Demodulation         : 1.31
% 15.07/6.48  BG Simplification    : 0.16
% 15.07/6.48  Subsumption          : 1.99
% 15.07/6.48  Abstraction          : 0.19
% 15.07/6.48  MUC search           : 0.00
% 15.07/6.48  Cooper               : 0.00
% 15.07/6.48  Total                : 5.74
% 15.07/6.48  Index Insertion      : 0.00
% 15.07/6.48  Index Deletion       : 0.00
% 15.07/6.48  Index Matching       : 0.00
% 15.07/6.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
