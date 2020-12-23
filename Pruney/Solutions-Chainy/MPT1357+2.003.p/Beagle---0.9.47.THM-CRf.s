%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:53 EST 2020

% Result     : Theorem 14.52s
% Output     : CNFRefutation 14.52s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 909 expanded)
%              Number of leaves         :   32 ( 322 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 (2572 expanded)
%              Number of equality atoms :   33 ( 595 expanded)
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

tff(f_120,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_116,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24387,plain,(
    ! [A_429] :
      ( u1_struct_0(A_429) = k2_struct_0(A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_24391,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_24387])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_24392,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24391,c_38])).

tff(c_24441,plain,(
    ! [A_440,B_441] :
      ( m1_pre_topc(k1_pre_topc(A_440,B_441),A_440)
      | ~ m1_subset_1(B_441,k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ l1_pre_topc(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24443,plain,(
    ! [B_441] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_441),'#skF_2')
      | ~ m1_subset_1(B_441,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24391,c_24441])).

tff(c_24466,plain,(
    ! [B_443] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_443),'#skF_2')
      | ~ m1_subset_1(B_443,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24443])).

tff(c_24474,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24392,c_24466])).

tff(c_44,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_121,plain,(
    ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_122,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_126,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_127,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_38])).

tff(c_175,plain,(
    ! [A_62,B_63] :
      ( m1_pre_topc(k1_pre_topc(A_62,B_63),A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [B_63] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_63),'#skF_2')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_175])).

tff(c_352,plain,(
    ! [B_73] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_73),'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_177])).

tff(c_360,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_352])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [A_64,B_65] :
      ( u1_struct_0(k1_pre_topc(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_187,plain,(
    ! [B_65] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_184])).

tff(c_215,plain,(
    ! [B_67] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_67)) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_187])).

tff(c_223,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_127,c_215])).

tff(c_20,plain,(
    ! [B_11,A_9] :
      ( l1_pre_topc(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_365,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_360,c_20])).

tff(c_368,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_365])).

tff(c_120,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_402,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_368,c_120])).

tff(c_404,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_402])).

tff(c_80,plain,
    ( v2_compts_1('#skF_3','#skF_2')
    | v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_132,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_80])).

tff(c_28,plain,(
    ! [A_22] :
      ( v2_compts_1(k2_struct_0(A_22),A_22)
      | ~ v1_compts_1(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_411,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_28])).

tff(c_417,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_132,c_411])).

tff(c_427,plain,(
    ! [A_76,B_77,C_78] :
      ( '#skF_1'(A_76,B_77,C_78) = C_78
      | v2_compts_1(C_78,A_76)
      | ~ r1_tarski(C_78,k2_struct_0(B_77))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1679,plain,(
    ! [A_115,B_116] :
      ( '#skF_1'(A_115,B_116,k2_struct_0(B_116)) = k2_struct_0(B_116)
      | v2_compts_1(k2_struct_0(B_116),A_115)
      | ~ m1_subset_1(k2_struct_0(B_116),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_pre_topc(B_116,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_6,c_427])).

tff(c_1714,plain,(
    ! [B_116] :
      ( '#skF_1'('#skF_2',B_116,k2_struct_0(B_116)) = k2_struct_0(B_116)
      | v2_compts_1(k2_struct_0(B_116),'#skF_2')
      | ~ m1_subset_1(k2_struct_0(B_116),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_116,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_1679])).

tff(c_24285,plain,(
    ! [B_428] :
      ( '#skF_1'('#skF_2',B_428,k2_struct_0(B_428)) = k2_struct_0(B_428)
      | v2_compts_1(k2_struct_0(B_428),'#skF_2')
      | ~ m1_subset_1(k2_struct_0(B_428),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_428,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1714])).

tff(c_24322,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_24285])).

tff(c_24356,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3'
    | v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_127,c_404,c_404,c_404,c_24322])).

tff(c_24357,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_24356])).

tff(c_32,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ v2_compts_1('#skF_1'(A_23,B_35,C_41),B_35)
      | v2_compts_1(C_41,A_23)
      | ~ r1_tarski(C_41,k2_struct_0(B_35))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_pre_topc(B_35,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24369,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24357,c_32])).

tff(c_24382,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_360,c_127,c_126,c_6,c_404,c_417,c_24369])).

tff(c_24384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_24382])).

tff(c_24386,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24385,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24483,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24474,c_20])).

tff(c_24486,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24483])).

tff(c_24529,plain,(
    ! [A_445,B_446] :
      ( u1_struct_0(k1_pre_topc(A_445,B_446)) = B_446
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24535,plain,(
    ! [B_446] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_446)) = B_446
      | ~ m1_subset_1(B_446,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24391,c_24529])).

tff(c_24629,plain,(
    ! [B_448] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_448)) = B_448
      | ~ m1_subset_1(B_448,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24535])).

tff(c_24637,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24392,c_24629])).

tff(c_24490,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24486,c_120])).

tff(c_24640,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24637,c_24490])).

tff(c_26,plain,(
    ! [A_22] :
      ( v1_compts_1(A_22)
      | ~ v2_compts_1(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24685,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24640,c_26])).

tff(c_24691,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24486,c_24685])).

tff(c_24692,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_24385,c_24691])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_25468,plain,(
    ! [D_486,B_487,A_488] :
      ( v2_compts_1(D_486,B_487)
      | ~ m1_subset_1(D_486,k1_zfmisc_1(u1_struct_0(B_487)))
      | ~ v2_compts_1(D_486,A_488)
      | ~ r1_tarski(D_486,k2_struct_0(B_487))
      | ~ m1_subset_1(D_486,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ m1_pre_topc(B_487,A_488)
      | ~ l1_pre_topc(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26321,plain,(
    ! [B_501,A_502] :
      ( v2_compts_1(u1_struct_0(B_501),B_501)
      | ~ v2_compts_1(u1_struct_0(B_501),A_502)
      | ~ r1_tarski(u1_struct_0(B_501),k2_struct_0(B_501))
      | ~ m1_subset_1(u1_struct_0(B_501),k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_pre_topc(B_501,A_502)
      | ~ l1_pre_topc(A_502) ) ),
    inference(resolution,[status(thm)],[c_101,c_25468])).

tff(c_26353,plain,(
    ! [A_502] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_pre_topc('#skF_2','#skF_3'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),A_502)
      | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_502)
      | ~ l1_pre_topc(A_502) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24637,c_26321])).

tff(c_26384,plain,(
    ! [A_502] :
      ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v2_compts_1('#skF_3',A_502)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_502)
      | ~ l1_pre_topc(A_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24637,c_6,c_24640,c_24637,c_24637,c_26353])).

tff(c_27771,plain,(
    ! [A_538] :
      ( ~ v2_compts_1('#skF_3',A_538)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_538)
      | ~ l1_pre_topc(A_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24692,c_26384])).

tff(c_27826,plain,
    ( ~ v2_compts_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24391,c_27771])).

tff(c_27851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24474,c_24392,c_24386,c_27826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.52/6.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.52/6.25  
% 14.52/6.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.52/6.25  %$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 14.52/6.25  
% 14.52/6.25  %Foreground sorts:
% 14.52/6.25  
% 14.52/6.25  
% 14.52/6.25  %Background operators:
% 14.52/6.25  
% 14.52/6.25  
% 14.52/6.25  %Foreground operators:
% 14.52/6.25  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 14.52/6.25  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 14.52/6.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.52/6.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.52/6.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.52/6.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.52/6.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.52/6.25  tff('#skF_2', type, '#skF_2': $i).
% 14.52/6.25  tff('#skF_3', type, '#skF_3': $i).
% 14.52/6.25  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 14.52/6.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.52/6.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.52/6.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.52/6.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.52/6.25  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.52/6.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.52/6.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.52/6.25  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 14.52/6.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.52/6.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.52/6.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.52/6.25  
% 14.52/6.27  tff(f_120, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 14.52/6.27  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.52/6.27  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 14.52/6.27  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 14.52/6.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.52/6.27  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 14.52/6.27  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 14.52/6.27  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 14.52/6.27  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 14.52/6.27  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 14.52/6.27  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.52/6.27  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.52/6.27  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.52/6.27  tff(c_116, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.52/6.27  tff(c_24387, plain, (![A_429]: (u1_struct_0(A_429)=k2_struct_0(A_429) | ~l1_pre_topc(A_429))), inference(resolution, [status(thm)], [c_18, c_116])).
% 14.52/6.27  tff(c_24391, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_24387])).
% 14.52/6.27  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.52/6.27  tff(c_24392, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24391, c_38])).
% 14.52/6.27  tff(c_24441, plain, (![A_440, B_441]: (m1_pre_topc(k1_pre_topc(A_440, B_441), A_440) | ~m1_subset_1(B_441, k1_zfmisc_1(u1_struct_0(A_440))) | ~l1_pre_topc(A_440))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.52/6.27  tff(c_24443, plain, (![B_441]: (m1_pre_topc(k1_pre_topc('#skF_2', B_441), '#skF_2') | ~m1_subset_1(B_441, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24391, c_24441])).
% 14.52/6.27  tff(c_24466, plain, (![B_443]: (m1_pre_topc(k1_pre_topc('#skF_2', B_443), '#skF_2') | ~m1_subset_1(B_443, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24443])).
% 14.52/6.27  tff(c_24474, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_24392, c_24466])).
% 14.52/6.27  tff(c_44, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.52/6.27  tff(c_121, plain, (~v2_compts_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 14.52/6.27  tff(c_122, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_18, c_116])).
% 14.52/6.27  tff(c_126, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_122])).
% 14.52/6.27  tff(c_127, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_38])).
% 14.52/6.27  tff(c_175, plain, (![A_62, B_63]: (m1_pre_topc(k1_pre_topc(A_62, B_63), A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.52/6.27  tff(c_177, plain, (![B_63]: (m1_pre_topc(k1_pre_topc('#skF_2', B_63), '#skF_2') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_175])).
% 14.52/6.27  tff(c_352, plain, (![B_73]: (m1_pre_topc(k1_pre_topc('#skF_2', B_73), '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_177])).
% 14.52/6.27  tff(c_360, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_127, c_352])).
% 14.52/6.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.52/6.27  tff(c_184, plain, (![A_64, B_65]: (u1_struct_0(k1_pre_topc(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.52/6.27  tff(c_187, plain, (![B_65]: (u1_struct_0(k1_pre_topc('#skF_2', B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_184])).
% 14.52/6.27  tff(c_215, plain, (![B_67]: (u1_struct_0(k1_pre_topc('#skF_2', B_67))=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_187])).
% 14.52/6.27  tff(c_223, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_127, c_215])).
% 14.52/6.27  tff(c_20, plain, (![B_11, A_9]: (l1_pre_topc(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.52/6.27  tff(c_365, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_360, c_20])).
% 14.52/6.27  tff(c_368, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_365])).
% 14.52/6.27  tff(c_120, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_18, c_116])).
% 14.52/6.27  tff(c_402, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_368, c_120])).
% 14.52/6.27  tff(c_404, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_402])).
% 14.52/6.27  tff(c_80, plain, (v2_compts_1('#skF_3', '#skF_2') | v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.52/6.27  tff(c_132, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_121, c_80])).
% 14.52/6.27  tff(c_28, plain, (![A_22]: (v2_compts_1(k2_struct_0(A_22), A_22) | ~v1_compts_1(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.52/6.27  tff(c_411, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_404, c_28])).
% 14.52/6.27  tff(c_417, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_132, c_411])).
% 14.52/6.27  tff(c_427, plain, (![A_76, B_77, C_78]: ('#skF_1'(A_76, B_77, C_78)=C_78 | v2_compts_1(C_78, A_76) | ~r1_tarski(C_78, k2_struct_0(B_77)) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_77, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.52/6.27  tff(c_1679, plain, (![A_115, B_116]: ('#skF_1'(A_115, B_116, k2_struct_0(B_116))=k2_struct_0(B_116) | v2_compts_1(k2_struct_0(B_116), A_115) | ~m1_subset_1(k2_struct_0(B_116), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_6, c_427])).
% 14.52/6.27  tff(c_1714, plain, (![B_116]: ('#skF_1'('#skF_2', B_116, k2_struct_0(B_116))=k2_struct_0(B_116) | v2_compts_1(k2_struct_0(B_116), '#skF_2') | ~m1_subset_1(k2_struct_0(B_116), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_116, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_1679])).
% 14.52/6.27  tff(c_24285, plain, (![B_428]: ('#skF_1'('#skF_2', B_428, k2_struct_0(B_428))=k2_struct_0(B_428) | v2_compts_1(k2_struct_0(B_428), '#skF_2') | ~m1_subset_1(k2_struct_0(B_428), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_428, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1714])).
% 14.52/6.27  tff(c_24322, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_404, c_24285])).
% 14.52/6.27  tff(c_24356, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3' | v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_127, c_404, c_404, c_404, c_24322])).
% 14.52/6.27  tff(c_24357, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_121, c_24356])).
% 14.52/6.27  tff(c_32, plain, (![A_23, B_35, C_41]: (~v2_compts_1('#skF_1'(A_23, B_35, C_41), B_35) | v2_compts_1(C_41, A_23) | ~r1_tarski(C_41, k2_struct_0(B_35)) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_pre_topc(B_35, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.52/6.27  tff(c_24369, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24357, c_32])).
% 14.52/6.27  tff(c_24382, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_360, c_127, c_126, c_6, c_404, c_417, c_24369])).
% 14.52/6.27  tff(c_24384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_24382])).
% 14.52/6.27  tff(c_24386, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 14.52/6.27  tff(c_24385, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 14.52/6.27  tff(c_24483, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24474, c_20])).
% 14.52/6.27  tff(c_24486, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24483])).
% 14.52/6.27  tff(c_24529, plain, (![A_445, B_446]: (u1_struct_0(k1_pre_topc(A_445, B_446))=B_446 | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.52/6.27  tff(c_24535, plain, (![B_446]: (u1_struct_0(k1_pre_topc('#skF_2', B_446))=B_446 | ~m1_subset_1(B_446, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24391, c_24529])).
% 14.52/6.27  tff(c_24629, plain, (![B_448]: (u1_struct_0(k1_pre_topc('#skF_2', B_448))=B_448 | ~m1_subset_1(B_448, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24535])).
% 14.52/6.27  tff(c_24637, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24392, c_24629])).
% 14.52/6.27  tff(c_24490, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24486, c_120])).
% 14.52/6.27  tff(c_24640, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24637, c_24490])).
% 14.52/6.27  tff(c_26, plain, (![A_22]: (v1_compts_1(A_22) | ~v2_compts_1(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.52/6.27  tff(c_24685, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24640, c_26])).
% 14.52/6.27  tff(c_24691, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24486, c_24685])).
% 14.52/6.27  tff(c_24692, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_24385, c_24691])).
% 14.52/6.27  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.52/6.27  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.52/6.27  tff(c_101, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 14.52/6.27  tff(c_25468, plain, (![D_486, B_487, A_488]: (v2_compts_1(D_486, B_487) | ~m1_subset_1(D_486, k1_zfmisc_1(u1_struct_0(B_487))) | ~v2_compts_1(D_486, A_488) | ~r1_tarski(D_486, k2_struct_0(B_487)) | ~m1_subset_1(D_486, k1_zfmisc_1(u1_struct_0(A_488))) | ~m1_pre_topc(B_487, A_488) | ~l1_pre_topc(A_488))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.52/6.27  tff(c_26321, plain, (![B_501, A_502]: (v2_compts_1(u1_struct_0(B_501), B_501) | ~v2_compts_1(u1_struct_0(B_501), A_502) | ~r1_tarski(u1_struct_0(B_501), k2_struct_0(B_501)) | ~m1_subset_1(u1_struct_0(B_501), k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_pre_topc(B_501, A_502) | ~l1_pre_topc(A_502))), inference(resolution, [status(thm)], [c_101, c_25468])).
% 14.52/6.27  tff(c_26353, plain, (![A_502]: (v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), A_502) | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_502) | ~l1_pre_topc(A_502))), inference(superposition, [status(thm), theory('equality')], [c_24637, c_26321])).
% 14.52/6.27  tff(c_26384, plain, (![A_502]: (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', A_502) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_502) | ~l1_pre_topc(A_502))), inference(demodulation, [status(thm), theory('equality')], [c_24637, c_6, c_24640, c_24637, c_24637, c_26353])).
% 14.52/6.27  tff(c_27771, plain, (![A_538]: (~v2_compts_1('#skF_3', A_538) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_538))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_538) | ~l1_pre_topc(A_538))), inference(negUnitSimplification, [status(thm)], [c_24692, c_26384])).
% 14.52/6.27  tff(c_27826, plain, (~v2_compts_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24391, c_27771])).
% 14.52/6.27  tff(c_27851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_24474, c_24392, c_24386, c_27826])).
% 14.52/6.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.52/6.27  
% 14.52/6.27  Inference rules
% 14.52/6.27  ----------------------
% 14.52/6.27  #Ref     : 0
% 14.52/6.27  #Sup     : 7366
% 14.52/6.27  #Fact    : 0
% 14.52/6.27  #Define  : 0
% 14.52/6.27  #Split   : 25
% 14.52/6.27  #Chain   : 0
% 14.52/6.27  #Close   : 0
% 14.52/6.27  
% 14.52/6.27  Ordering : KBO
% 14.52/6.27  
% 14.52/6.27  Simplification rules
% 14.52/6.27  ----------------------
% 14.52/6.27  #Subsume      : 1035
% 14.52/6.27  #Demod        : 6297
% 14.52/6.27  #Tautology    : 1356
% 14.52/6.27  #SimpNegUnit  : 28
% 14.52/6.27  #BackRed      : 3
% 14.52/6.27  
% 14.52/6.27  #Partial instantiations: 0
% 14.52/6.27  #Strategies tried      : 1
% 14.52/6.27  
% 14.52/6.27  Timing (in seconds)
% 14.52/6.27  ----------------------
% 14.52/6.27  Preprocessing        : 0.32
% 14.52/6.27  Parsing              : 0.16
% 14.52/6.27  CNF conversion       : 0.02
% 14.52/6.27  Main loop            : 5.15
% 14.52/6.27  Inferencing          : 0.97
% 14.52/6.27  Reduction            : 1.70
% 14.52/6.27  Demodulation         : 1.28
% 14.52/6.27  BG Simplification    : 0.15
% 14.52/6.27  Subsumption          : 2.06
% 14.52/6.27  Abstraction          : 0.21
% 14.52/6.27  MUC search           : 0.00
% 14.52/6.27  Cooper               : 0.00
% 14.52/6.27  Total                : 5.51
% 14.52/6.27  Index Insertion      : 0.00
% 14.52/6.27  Index Deletion       : 0.00
% 14.52/6.27  Index Matching       : 0.00
% 14.52/6.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
