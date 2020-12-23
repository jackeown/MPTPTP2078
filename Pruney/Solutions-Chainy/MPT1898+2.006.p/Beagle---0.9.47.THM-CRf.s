%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 177 expanded)
%              Number of leaves         :   33 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 ( 532 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_12,c_57])).

tff(c_50,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_207,plain,(
    ! [A_86,B_87] :
      ( r1_tarski('#skF_3'(A_86,B_87),B_87)
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_238,plain,(
    ! [A_90] :
      ( r1_tarski('#skF_3'(A_90,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_12,c_207])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,(
    ! [A_90] :
      ( '#skF_3'(A_90,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_3'(A_90,k1_xboole_0))
      | v2_tex_2(k1_xboole_0,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_238,c_2])).

tff(c_250,plain,(
    ! [A_90] :
      ( '#skF_3'(A_90,k1_xboole_0) = k1_xboole_0
      | v2_tex_2(k1_xboole_0,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_245])).

tff(c_504,plain,(
    ! [A_136,B_137] :
      ( m1_subset_1('#skF_4'(A_136,B_137),k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v2_tex_2(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v3_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    ! [B_48] :
      ( ~ v3_tex_2(B_48,'#skF_5')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_522,plain,(
    ! [B_137] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_137),'#skF_5')
      | ~ v2_tex_2(B_137,'#skF_5')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_504,c_44])).

tff(c_537,plain,(
    ! [B_137] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_137),'#skF_5')
      | ~ v2_tex_2(B_137,'#skF_5')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_522])).

tff(c_540,plain,(
    ! [B_138] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_138),'#skF_5')
      | ~ v2_tex_2(B_138,'#skF_5')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_537])).

tff(c_573,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5')
    | ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_540])).

tff(c_574,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_577,plain,
    ( '#skF_3'('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_250,c_574])).

tff(c_580,plain,(
    '#skF_3'('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_577])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_61,c_96])).

tff(c_124,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_20,plain,(
    ! [A_14] :
      ( v4_pre_topc('#skF_1'(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_14] :
      ( m1_subset_1('#skF_1'(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_168,plain,(
    ! [A_80] :
      ( m1_subset_1('#skF_1'(A_80),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( k9_subset_1(A_5,B_6,C_7) = k3_xboole_0(B_6,C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_80,B_6] :
      ( k9_subset_1(u1_struct_0(A_80),B_6,'#skF_1'(A_80)) = k3_xboole_0(B_6,'#skF_1'(A_80))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_168,c_10])).

tff(c_793,plain,(
    ! [A_154,B_155,D_156] :
      ( k9_subset_1(u1_struct_0(A_154),B_155,D_156) != '#skF_3'(A_154,B_155)
      | ~ v4_pre_topc(D_156,A_154)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | v2_tex_2(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4472,plain,(
    ! [B_452,A_453] :
      ( k3_xboole_0(B_452,'#skF_1'(A_453)) != '#skF_3'(A_453,B_452)
      | ~ v4_pre_topc('#skF_1'(A_453),A_453)
      | ~ m1_subset_1('#skF_1'(A_453),k1_zfmisc_1(u1_struct_0(A_453)))
      | v2_tex_2(B_452,A_453)
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_453)))
      | ~ l1_pre_topc(A_453)
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453)
      | v2_struct_0(A_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_793])).

tff(c_4480,plain,(
    ! [B_454,A_455] :
      ( k3_xboole_0(B_454,'#skF_1'(A_455)) != '#skF_3'(A_455,B_454)
      | ~ v4_pre_topc('#skF_1'(A_455),A_455)
      | v2_tex_2(B_454,A_455)
      | ~ m1_subset_1(B_454,k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455)
      | v2_struct_0(A_455) ) ),
    inference(resolution,[status(thm)],[c_24,c_4472])).

tff(c_4484,plain,(
    ! [B_456,A_457] :
      ( k3_xboole_0(B_456,'#skF_1'(A_457)) != '#skF_3'(A_457,B_456)
      | v2_tex_2(B_456,A_457)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_20,c_4480])).

tff(c_4504,plain,(
    ! [A_457] :
      ( k3_xboole_0(k1_xboole_0,'#skF_1'(A_457)) != '#skF_3'(A_457,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_457)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_12,c_4484])).

tff(c_4512,plain,(
    ! [A_458] :
      ( '#skF_3'(A_458,k1_xboole_0) != k1_xboole_0
      | v2_tex_2(k1_xboole_0,A_458)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_4504])).

tff(c_4515,plain,
    ( '#skF_3'('#skF_5',k1_xboole_0) != k1_xboole_0
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4512,c_574])).

tff(c_4518,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_580,c_4515])).

tff(c_4520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4518])).

tff(c_4522,plain,(
    v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_421,plain,(
    ! [A_118,B_119] :
      ( v3_tex_2('#skF_4'(A_118,B_119),A_118)
      | ~ v2_tex_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v3_tdlat_3(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_434,plain,(
    ! [A_118,A_9] :
      ( v3_tex_2('#skF_4'(A_118,A_9),A_118)
      | ~ v2_tex_2(A_9,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v3_tdlat_3(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118)
      | ~ r1_tarski(A_9,u1_struct_0(A_118)) ) ),
    inference(resolution,[status(thm)],[c_16,c_421])).

tff(c_4521,plain,(
    ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_4525,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_434,c_4521])).

tff(c_4531,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_50,c_48,c_46,c_4522,c_4525])).

tff(c_4533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.95/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.36  
% 6.95/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.36  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 6.95/2.36  
% 6.95/2.36  %Foreground sorts:
% 6.95/2.36  
% 6.95/2.36  
% 6.95/2.36  %Background operators:
% 6.95/2.36  
% 6.95/2.36  
% 6.95/2.36  %Foreground operators:
% 6.95/2.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.95/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.95/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.95/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.95/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.95/2.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.95/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.95/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.95/2.36  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.95/2.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.95/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.95/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.95/2.36  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 6.95/2.36  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.95/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.95/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.95/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.95/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.95/2.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.95/2.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.95/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.95/2.36  
% 6.95/2.38  tff(f_123, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 6.95/2.38  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.95/2.38  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.95/2.38  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 6.95/2.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.95/2.38  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 6.95/2.38  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.95/2.38  tff(f_64, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 6.95/2.38  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.95/2.38  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.95/2.38  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.95/2.38  tff(c_57, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.95/2.38  tff(c_61, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_12, c_57])).
% 6.95/2.38  tff(c_50, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.95/2.38  tff(c_48, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.95/2.38  tff(c_46, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.95/2.38  tff(c_207, plain, (![A_86, B_87]: (r1_tarski('#skF_3'(A_86, B_87), B_87) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.95/2.38  tff(c_238, plain, (![A_90]: (r1_tarski('#skF_3'(A_90, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_12, c_207])).
% 6.95/2.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.38  tff(c_245, plain, (![A_90]: ('#skF_3'(A_90, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_3'(A_90, k1_xboole_0)) | v2_tex_2(k1_xboole_0, A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_238, c_2])).
% 6.95/2.38  tff(c_250, plain, (![A_90]: ('#skF_3'(A_90, k1_xboole_0)=k1_xboole_0 | v2_tex_2(k1_xboole_0, A_90) | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_245])).
% 6.95/2.38  tff(c_504, plain, (![A_136, B_137]: (m1_subset_1('#skF_4'(A_136, B_137), k1_zfmisc_1(u1_struct_0(A_136))) | ~v2_tex_2(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v3_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.95/2.38  tff(c_44, plain, (![B_48]: (~v3_tex_2(B_48, '#skF_5') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.95/2.38  tff(c_522, plain, (![B_137]: (~v3_tex_2('#skF_4'('#skF_5', B_137), '#skF_5') | ~v2_tex_2(B_137, '#skF_5') | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_504, c_44])).
% 6.95/2.38  tff(c_537, plain, (![B_137]: (~v3_tex_2('#skF_4'('#skF_5', B_137), '#skF_5') | ~v2_tex_2(B_137, '#skF_5') | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_522])).
% 6.95/2.38  tff(c_540, plain, (![B_138]: (~v3_tex_2('#skF_4'('#skF_5', B_138), '#skF_5') | ~v2_tex_2(B_138, '#skF_5') | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_537])).
% 6.95/2.38  tff(c_573, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5') | ~v2_tex_2(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_12, c_540])).
% 6.95/2.38  tff(c_574, plain, (~v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_573])).
% 6.95/2.38  tff(c_577, plain, ('#skF_3'('#skF_5', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_250, c_574])).
% 6.95/2.38  tff(c_580, plain, ('#skF_3'('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_577])).
% 6.95/2.38  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.38  tff(c_96, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.38  tff(c_109, plain, (![A_63]: (k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_61, c_96])).
% 6.95/2.38  tff(c_124, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_109])).
% 6.95/2.38  tff(c_20, plain, (![A_14]: (v4_pre_topc('#skF_1'(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.95/2.38  tff(c_24, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.95/2.38  tff(c_168, plain, (![A_80]: (m1_subset_1('#skF_1'(A_80), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.95/2.38  tff(c_10, plain, (![A_5, B_6, C_7]: (k9_subset_1(A_5, B_6, C_7)=k3_xboole_0(B_6, C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.95/2.38  tff(c_180, plain, (![A_80, B_6]: (k9_subset_1(u1_struct_0(A_80), B_6, '#skF_1'(A_80))=k3_xboole_0(B_6, '#skF_1'(A_80)) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(resolution, [status(thm)], [c_168, c_10])).
% 6.95/2.38  tff(c_793, plain, (![A_154, B_155, D_156]: (k9_subset_1(u1_struct_0(A_154), B_155, D_156)!='#skF_3'(A_154, B_155) | ~v4_pre_topc(D_156, A_154) | ~m1_subset_1(D_156, k1_zfmisc_1(u1_struct_0(A_154))) | v2_tex_2(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.95/2.38  tff(c_4472, plain, (![B_452, A_453]: (k3_xboole_0(B_452, '#skF_1'(A_453))!='#skF_3'(A_453, B_452) | ~v4_pre_topc('#skF_1'(A_453), A_453) | ~m1_subset_1('#skF_1'(A_453), k1_zfmisc_1(u1_struct_0(A_453))) | v2_tex_2(B_452, A_453) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(A_453))) | ~l1_pre_topc(A_453) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453) | v2_struct_0(A_453))), inference(superposition, [status(thm), theory('equality')], [c_180, c_793])).
% 6.95/2.38  tff(c_4480, plain, (![B_454, A_455]: (k3_xboole_0(B_454, '#skF_1'(A_455))!='#skF_3'(A_455, B_454) | ~v4_pre_topc('#skF_1'(A_455), A_455) | v2_tex_2(B_454, A_455) | ~m1_subset_1(B_454, k1_zfmisc_1(u1_struct_0(A_455))) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455) | v2_struct_0(A_455))), inference(resolution, [status(thm)], [c_24, c_4472])).
% 6.95/2.38  tff(c_4484, plain, (![B_456, A_457]: (k3_xboole_0(B_456, '#skF_1'(A_457))!='#skF_3'(A_457, B_456) | v2_tex_2(B_456, A_457) | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(resolution, [status(thm)], [c_20, c_4480])).
% 6.95/2.38  tff(c_4504, plain, (![A_457]: (k3_xboole_0(k1_xboole_0, '#skF_1'(A_457))!='#skF_3'(A_457, k1_xboole_0) | v2_tex_2(k1_xboole_0, A_457) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(resolution, [status(thm)], [c_12, c_4484])).
% 6.95/2.38  tff(c_4512, plain, (![A_458]: ('#skF_3'(A_458, k1_xboole_0)!=k1_xboole_0 | v2_tex_2(k1_xboole_0, A_458) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_4504])).
% 6.95/2.38  tff(c_4515, plain, ('#skF_3'('#skF_5', k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4512, c_574])).
% 6.95/2.38  tff(c_4518, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_580, c_4515])).
% 6.95/2.38  tff(c_4520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_4518])).
% 6.95/2.38  tff(c_4522, plain, (v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_573])).
% 6.95/2.38  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.95/2.38  tff(c_421, plain, (![A_118, B_119]: (v3_tex_2('#skF_4'(A_118, B_119), A_118) | ~v2_tex_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v3_tdlat_3(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.95/2.38  tff(c_434, plain, (![A_118, A_9]: (v3_tex_2('#skF_4'(A_118, A_9), A_118) | ~v2_tex_2(A_9, A_118) | ~l1_pre_topc(A_118) | ~v3_tdlat_3(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118) | ~r1_tarski(A_9, u1_struct_0(A_118)))), inference(resolution, [status(thm)], [c_16, c_421])).
% 6.95/2.38  tff(c_4521, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5')), inference(splitRight, [status(thm)], [c_573])).
% 6.95/2.38  tff(c_4525, plain, (~v2_tex_2(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_434, c_4521])).
% 6.95/2.38  tff(c_4531, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_50, c_48, c_46, c_4522, c_4525])).
% 6.95/2.38  tff(c_4533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_4531])).
% 6.95/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.38  
% 6.95/2.38  Inference rules
% 6.95/2.38  ----------------------
% 6.95/2.38  #Ref     : 0
% 6.95/2.38  #Sup     : 987
% 6.95/2.38  #Fact    : 0
% 6.95/2.38  #Define  : 0
% 6.95/2.38  #Split   : 5
% 6.95/2.38  #Chain   : 0
% 6.95/2.38  #Close   : 0
% 6.95/2.38  
% 6.95/2.38  Ordering : KBO
% 6.95/2.38  
% 6.95/2.38  Simplification rules
% 6.95/2.38  ----------------------
% 6.95/2.38  #Subsume      : 176
% 6.95/2.38  #Demod        : 575
% 6.95/2.38  #Tautology    : 328
% 6.95/2.38  #SimpNegUnit  : 66
% 6.95/2.38  #BackRed      : 1
% 6.95/2.38  
% 6.95/2.38  #Partial instantiations: 0
% 6.95/2.38  #Strategies tried      : 1
% 6.95/2.38  
% 6.95/2.38  Timing (in seconds)
% 6.95/2.38  ----------------------
% 6.95/2.38  Preprocessing        : 0.34
% 6.95/2.38  Parsing              : 0.17
% 6.95/2.38  CNF conversion       : 0.03
% 6.95/2.38  Main loop            : 1.28
% 6.95/2.38  Inferencing          : 0.52
% 6.95/2.38  Reduction            : 0.36
% 6.95/2.38  Demodulation         : 0.24
% 6.95/2.38  BG Simplification    : 0.06
% 6.95/2.38  Subsumption          : 0.27
% 6.95/2.38  Abstraction          : 0.08
% 6.95/2.38  MUC search           : 0.00
% 6.95/2.38  Cooper               : 0.00
% 6.95/2.38  Total                : 1.65
% 6.95/2.38  Index Insertion      : 0.00
% 6.95/2.38  Index Deletion       : 0.00
% 6.95/2.38  Index Matching       : 0.00
% 6.95/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
