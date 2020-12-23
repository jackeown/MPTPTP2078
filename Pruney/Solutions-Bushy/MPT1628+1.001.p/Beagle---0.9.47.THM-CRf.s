%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:08 EST 2020

% Result     : Theorem 9.12s
% Output     : CNFRefutation 9.26s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 343 expanded)
%              Number of leaves         :   33 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  644 (1543 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C,D] :
                ( r1_tarski(C,D)
               => ( ( r1_waybel_0(A,B,C)
                   => r1_waybel_0(A,B,D) )
                  & ( r2_waybel_0(A,B,C)
                   => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_75,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,
    ( r1_waybel_0('#skF_6','#skF_7','#skF_8')
    | r2_waybel_0('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_64,plain,(
    r2_waybel_0('#skF_6','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_22,plain,(
    ! [A_107] : m1_subset_1('#skF_5'(A_107),A_107) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_54,B_82,C_96] :
      ( m1_subset_1('#skF_3'(A_54,B_82,C_96),u1_struct_0(B_82))
      | r2_waybel_0(A_54,B_82,C_96)
      | ~ l1_waybel_0(B_82,A_54)
      | v2_struct_0(B_82)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(A_109,B_110)
      | v1_xboole_0(B_110)
      | ~ m1_subset_1(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(A_111,k1_zfmisc_1(B_112))
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [C_134,B_135,A_136] :
      ( ~ v1_xboole_0(C_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(C_134))
      | ~ r2_hidden(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_82,plain,(
    ! [B_139,A_140,A_141] :
      ( ~ v1_xboole_0(B_139)
      | ~ r2_hidden(A_140,A_141)
      | ~ r1_tarski(A_141,B_139) ) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_104,plain,(
    ! [B_150,B_151,A_152] :
      ( ~ v1_xboole_0(B_150)
      | ~ r1_tarski(B_151,B_150)
      | v1_xboole_0(B_151)
      | ~ m1_subset_1(A_152,B_151) ) ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_110,plain,(
    ! [A_152] :
      ( ~ v1_xboole_0('#skF_9')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_152,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_104])).

tff(c_111,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_16,plain,(
    ! [A_54,B_82,C_96,D_105] :
      ( m1_subset_1('#skF_4'(A_54,B_82,C_96,D_105),u1_struct_0(B_82))
      | ~ m1_subset_1(D_105,u1_struct_0(B_82))
      | ~ r2_waybel_0(A_54,B_82,C_96)
      | ~ l1_waybel_0(B_82,A_54)
      | v2_struct_0(B_82)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_295,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( r2_hidden(k2_waybel_0(A_210,B_211,'#skF_4'(A_210,B_211,C_212,D_213)),C_212)
      | ~ m1_subset_1(D_213,u1_struct_0(B_211))
      | ~ r2_waybel_0(A_210,B_211,C_212)
      | ~ l1_waybel_0(B_211,A_210)
      | v2_struct_0(B_211)
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    ! [A_142,C_143,B_144] :
      ( m1_subset_1(A_142,C_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(C_143))
      | ~ r2_hidden(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_92,plain,(
    ! [A_142,B_112,A_111] :
      ( m1_subset_1(A_142,B_112)
      | ~ r2_hidden(A_142,A_111)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_338,plain,(
    ! [B_211,A_210,C_212,D_213,B_112] :
      ( m1_subset_1(k2_waybel_0(A_210,B_211,'#skF_4'(A_210,B_211,C_212,D_213)),B_112)
      | ~ r1_tarski(C_212,B_112)
      | ~ m1_subset_1(D_213,u1_struct_0(B_211))
      | ~ r2_waybel_0(A_210,B_211,C_212)
      | ~ l1_waybel_0(B_211,A_210)
      | v2_struct_0(B_211)
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_295,c_92])).

tff(c_14,plain,(
    ! [B_82,D_105,A_54,C_96] :
      ( r1_orders_2(B_82,D_105,'#skF_4'(A_54,B_82,C_96,D_105))
      | ~ m1_subset_1(D_105,u1_struct_0(B_82))
      | ~ r2_waybel_0(A_54,B_82,C_96)
      | ~ l1_waybel_0(B_82,A_54)
      | v2_struct_0(B_82)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_342,plain,(
    ! [A_214,B_215,E_216,C_217] :
      ( ~ r2_hidden(k2_waybel_0(A_214,B_215,E_216),C_217)
      | ~ r1_orders_2(B_215,'#skF_3'(A_214,B_215,C_217),E_216)
      | ~ m1_subset_1(E_216,u1_struct_0(B_215))
      | r2_waybel_0(A_214,B_215,C_217)
      | ~ l1_waybel_0(B_215,A_214)
      | v2_struct_0(B_215)
      | ~ l1_struct_0(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_860,plain,(
    ! [A_288,C_289,B_290,A_286,C_287] :
      ( ~ r2_hidden(k2_waybel_0(A_288,B_290,'#skF_4'(A_286,B_290,C_287,'#skF_3'(A_288,B_290,C_289))),C_289)
      | ~ m1_subset_1('#skF_4'(A_286,B_290,C_287,'#skF_3'(A_288,B_290,C_289)),u1_struct_0(B_290))
      | r2_waybel_0(A_288,B_290,C_289)
      | ~ l1_waybel_0(B_290,A_288)
      | ~ l1_struct_0(A_288)
      | v2_struct_0(A_288)
      | ~ m1_subset_1('#skF_3'(A_288,B_290,C_289),u1_struct_0(B_290))
      | ~ r2_waybel_0(A_286,B_290,C_287)
      | ~ l1_waybel_0(B_290,A_286)
      | v2_struct_0(B_290)
      | ~ l1_struct_0(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_14,c_342])).

tff(c_2224,plain,(
    ! [B_479,A_478,C_475,B_476,A_477] :
      ( ~ m1_subset_1('#skF_4'(A_478,B_479,C_475,'#skF_3'(A_477,B_479,B_476)),u1_struct_0(B_479))
      | r2_waybel_0(A_477,B_479,B_476)
      | ~ l1_waybel_0(B_479,A_477)
      | ~ l1_struct_0(A_477)
      | v2_struct_0(A_477)
      | ~ m1_subset_1('#skF_3'(A_477,B_479,B_476),u1_struct_0(B_479))
      | ~ r2_waybel_0(A_478,B_479,C_475)
      | ~ l1_waybel_0(B_479,A_478)
      | v2_struct_0(B_479)
      | ~ l1_struct_0(A_478)
      | v2_struct_0(A_478)
      | v1_xboole_0(B_476)
      | ~ m1_subset_1(k2_waybel_0(A_477,B_479,'#skF_4'(A_478,B_479,C_475,'#skF_3'(A_477,B_479,B_476))),B_476) ) ),
    inference(resolution,[status(thm)],[c_24,c_860])).

tff(c_2250,plain,(
    ! [A_480,B_481,C_482,B_483] :
      ( ~ m1_subset_1('#skF_4'(A_480,B_481,C_482,'#skF_3'(A_480,B_481,B_483)),u1_struct_0(B_481))
      | r2_waybel_0(A_480,B_481,B_483)
      | v1_xboole_0(B_483)
      | ~ r1_tarski(C_482,B_483)
      | ~ m1_subset_1('#skF_3'(A_480,B_481,B_483),u1_struct_0(B_481))
      | ~ r2_waybel_0(A_480,B_481,C_482)
      | ~ l1_waybel_0(B_481,A_480)
      | v2_struct_0(B_481)
      | ~ l1_struct_0(A_480)
      | v2_struct_0(A_480) ) ),
    inference(resolution,[status(thm)],[c_338,c_2224])).

tff(c_2256,plain,(
    ! [A_484,B_485,B_486,C_487] :
      ( r2_waybel_0(A_484,B_485,B_486)
      | v1_xboole_0(B_486)
      | ~ r1_tarski(C_487,B_486)
      | ~ m1_subset_1('#skF_3'(A_484,B_485,B_486),u1_struct_0(B_485))
      | ~ r2_waybel_0(A_484,B_485,C_487)
      | ~ l1_waybel_0(B_485,A_484)
      | v2_struct_0(B_485)
      | ~ l1_struct_0(A_484)
      | v2_struct_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_16,c_2250])).

tff(c_2286,plain,(
    ! [A_484,B_485] :
      ( r2_waybel_0(A_484,B_485,'#skF_9')
      | v1_xboole_0('#skF_9')
      | ~ m1_subset_1('#skF_3'(A_484,B_485,'#skF_9'),u1_struct_0(B_485))
      | ~ r2_waybel_0(A_484,B_485,'#skF_8')
      | ~ l1_waybel_0(B_485,A_484)
      | v2_struct_0(B_485)
      | ~ l1_struct_0(A_484)
      | v2_struct_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_34,c_2256])).

tff(c_2304,plain,(
    ! [A_488,B_489] :
      ( r2_waybel_0(A_488,B_489,'#skF_9')
      | ~ m1_subset_1('#skF_3'(A_488,B_489,'#skF_9'),u1_struct_0(B_489))
      | ~ r2_waybel_0(A_488,B_489,'#skF_8')
      | ~ l1_waybel_0(B_489,A_488)
      | v2_struct_0(B_489)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2286])).

tff(c_2310,plain,(
    ! [A_490,B_491] :
      ( ~ r2_waybel_0(A_490,B_491,'#skF_8')
      | r2_waybel_0(A_490,B_491,'#skF_9')
      | ~ l1_waybel_0(B_491,A_490)
      | v2_struct_0(B_491)
      | ~ l1_struct_0(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_20,c_2304])).

tff(c_44,plain,
    ( ~ r1_waybel_0('#skF_6','#skF_7','#skF_9')
    | ~ r2_waybel_0('#skF_6','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    ~ r2_waybel_0('#skF_6','#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_2315,plain,
    ( ~ r2_waybel_0('#skF_6','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2310,c_66])).

tff(c_2319,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_64,c_2315])).

tff(c_2321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_2319])).

tff(c_2323,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_2515,plain,(
    ! [A_550,B_551,C_552,D_553] :
      ( r2_hidden(k2_waybel_0(A_550,B_551,'#skF_4'(A_550,B_551,C_552,D_553)),C_552)
      | ~ m1_subset_1(D_553,u1_struct_0(B_551))
      | ~ r2_waybel_0(A_550,B_551,C_552)
      | ~ l1_waybel_0(B_551,A_550)
      | v2_struct_0(B_551)
      | ~ l1_struct_0(A_550)
      | v2_struct_0(A_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_74,plain,(
    ! [B_112,A_136,A_111] :
      ( ~ v1_xboole_0(B_112)
      | ~ r2_hidden(A_136,A_111)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_2591,plain,(
    ! [C_562,B_565,D_561,A_563,B_564] :
      ( ~ v1_xboole_0(B_564)
      | ~ r1_tarski(C_562,B_564)
      | ~ m1_subset_1(D_561,u1_struct_0(B_565))
      | ~ r2_waybel_0(A_563,B_565,C_562)
      | ~ l1_waybel_0(B_565,A_563)
      | v2_struct_0(B_565)
      | ~ l1_struct_0(A_563)
      | v2_struct_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_2515,c_74])).

tff(c_2601,plain,(
    ! [D_561,B_565,A_563] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ m1_subset_1(D_561,u1_struct_0(B_565))
      | ~ r2_waybel_0(A_563,B_565,'#skF_8')
      | ~ l1_waybel_0(B_565,A_563)
      | v2_struct_0(B_565)
      | ~ l1_struct_0(A_563)
      | v2_struct_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_34,c_2591])).

tff(c_2609,plain,(
    ! [D_566,B_567,A_568] :
      ( ~ m1_subset_1(D_566,u1_struct_0(B_567))
      | ~ r2_waybel_0(A_568,B_567,'#skF_8')
      | ~ l1_waybel_0(B_567,A_568)
      | v2_struct_0(B_567)
      | ~ l1_struct_0(A_568)
      | v2_struct_0(A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2323,c_2601])).

tff(c_2637,plain,(
    ! [A_569,B_570] :
      ( ~ r2_waybel_0(A_569,B_570,'#skF_8')
      | ~ l1_waybel_0(B_570,A_569)
      | v2_struct_0(B_570)
      | ~ l1_struct_0(A_569)
      | v2_struct_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_22,c_2609])).

tff(c_2640,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_2637])).

tff(c_2643,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_2640])).

tff(c_2645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_2643])).

tff(c_2647,plain,(
    r2_waybel_0('#skF_6','#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( r1_waybel_0('#skF_6','#skF_7','#skF_8')
    | ~ r2_waybel_0('#skF_6','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2649,plain,(
    r1_waybel_0('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_46])).

tff(c_4,plain,(
    ! [A_1,B_29,C_43] :
      ( m1_subset_1('#skF_2'(A_1,B_29,C_43),u1_struct_0(B_29))
      | ~ r1_waybel_0(A_1,B_29,C_43)
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2651,plain,(
    ! [C_573,B_574,A_575] :
      ( ~ v1_xboole_0(C_573)
      | ~ m1_subset_1(B_574,k1_zfmisc_1(C_573))
      | ~ r2_hidden(A_575,B_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2665,plain,(
    ! [B_578,A_579,A_580] :
      ( ~ v1_xboole_0(B_578)
      | ~ r2_hidden(A_579,A_580)
      | ~ r1_tarski(A_580,B_578) ) ),
    inference(resolution,[status(thm)],[c_28,c_2651])).

tff(c_2688,plain,(
    ! [B_592,B_593,A_594] :
      ( ~ v1_xboole_0(B_592)
      | ~ r1_tarski(B_593,B_592)
      | v1_xboole_0(B_593)
      | ~ m1_subset_1(A_594,B_593) ) ),
    inference(resolution,[status(thm)],[c_24,c_2665])).

tff(c_2694,plain,(
    ! [A_594] :
      ( ~ v1_xboole_0('#skF_9')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_594,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2688])).

tff(c_2695,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2694])).

tff(c_10,plain,(
    ! [A_1,B_29,C_43,D_50] :
      ( m1_subset_1('#skF_1'(A_1,B_29,C_43,D_50),u1_struct_0(B_29))
      | r1_waybel_0(A_1,B_29,C_43)
      | ~ m1_subset_1(D_50,u1_struct_0(B_29))
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [B_29,D_50,A_1,C_43] :
      ( r1_orders_2(B_29,D_50,'#skF_1'(A_1,B_29,C_43,D_50))
      | r1_waybel_0(A_1,B_29,C_43)
      | ~ m1_subset_1(D_50,u1_struct_0(B_29))
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2994,plain,(
    ! [A_666,B_667,E_668,C_669] :
      ( r2_hidden(k2_waybel_0(A_666,B_667,E_668),C_669)
      | ~ r1_orders_2(B_667,'#skF_2'(A_666,B_667,C_669),E_668)
      | ~ m1_subset_1(E_668,u1_struct_0(B_667))
      | ~ r1_waybel_0(A_666,B_667,C_669)
      | ~ l1_waybel_0(B_667,A_666)
      | v2_struct_0(B_667)
      | ~ l1_struct_0(A_666)
      | v2_struct_0(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3103,plain,(
    ! [A_691,B_690,C_689,A_688,C_687] :
      ( r2_hidden(k2_waybel_0(A_688,B_690,'#skF_1'(A_691,B_690,C_687,'#skF_2'(A_688,B_690,C_689))),C_689)
      | ~ m1_subset_1('#skF_1'(A_691,B_690,C_687,'#skF_2'(A_688,B_690,C_689)),u1_struct_0(B_690))
      | ~ r1_waybel_0(A_688,B_690,C_689)
      | ~ l1_waybel_0(B_690,A_688)
      | ~ l1_struct_0(A_688)
      | v2_struct_0(A_688)
      | r1_waybel_0(A_691,B_690,C_687)
      | ~ m1_subset_1('#skF_2'(A_688,B_690,C_689),u1_struct_0(B_690))
      | ~ l1_waybel_0(B_690,A_691)
      | v2_struct_0(B_690)
      | ~ l1_struct_0(A_691)
      | v2_struct_0(A_691) ) ),
    inference(resolution,[status(thm)],[c_8,c_2994])).

tff(c_2669,plain,(
    ! [A_581,C_582,B_583] :
      ( m1_subset_1(A_581,C_582)
      | ~ m1_subset_1(B_583,k1_zfmisc_1(C_582))
      | ~ r2_hidden(A_581,B_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2675,plain,(
    ! [A_581,B_112,A_111] :
      ( m1_subset_1(A_581,B_112)
      | ~ r2_hidden(A_581,A_111)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_2669])).

tff(c_5147,plain,(
    ! [C_974,C_971,A_972,B_973,A_975,B_976] :
      ( m1_subset_1(k2_waybel_0(A_975,B_973,'#skF_1'(A_972,B_973,C_971,'#skF_2'(A_975,B_973,C_974))),B_976)
      | ~ r1_tarski(C_974,B_976)
      | ~ m1_subset_1('#skF_1'(A_972,B_973,C_971,'#skF_2'(A_975,B_973,C_974)),u1_struct_0(B_973))
      | ~ r1_waybel_0(A_975,B_973,C_974)
      | ~ l1_waybel_0(B_973,A_975)
      | ~ l1_struct_0(A_975)
      | v2_struct_0(A_975)
      | r1_waybel_0(A_972,B_973,C_971)
      | ~ m1_subset_1('#skF_2'(A_975,B_973,C_974),u1_struct_0(B_973))
      | ~ l1_waybel_0(B_973,A_972)
      | v2_struct_0(B_973)
      | ~ l1_struct_0(A_972)
      | v2_struct_0(A_972) ) ),
    inference(resolution,[status(thm)],[c_3103,c_2675])).

tff(c_2953,plain,(
    ! [A_659,B_660,C_661,D_662] :
      ( ~ r2_hidden(k2_waybel_0(A_659,B_660,'#skF_1'(A_659,B_660,C_661,D_662)),C_661)
      | r1_waybel_0(A_659,B_660,C_661)
      | ~ m1_subset_1(D_662,u1_struct_0(B_660))
      | ~ l1_waybel_0(B_660,A_659)
      | v2_struct_0(B_660)
      | ~ l1_struct_0(A_659)
      | v2_struct_0(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2958,plain,(
    ! [A_659,B_660,B_110,D_662] :
      ( r1_waybel_0(A_659,B_660,B_110)
      | ~ m1_subset_1(D_662,u1_struct_0(B_660))
      | ~ l1_waybel_0(B_660,A_659)
      | v2_struct_0(B_660)
      | ~ l1_struct_0(A_659)
      | v2_struct_0(A_659)
      | v1_xboole_0(B_110)
      | ~ m1_subset_1(k2_waybel_0(A_659,B_660,'#skF_1'(A_659,B_660,B_110,D_662)),B_110) ) ),
    inference(resolution,[status(thm)],[c_24,c_2953])).

tff(c_5190,plain,(
    ! [B_977,C_978,A_979,B_980] :
      ( v1_xboole_0(B_977)
      | ~ r1_tarski(C_978,B_977)
      | ~ m1_subset_1('#skF_1'(A_979,B_980,B_977,'#skF_2'(A_979,B_980,C_978)),u1_struct_0(B_980))
      | ~ r1_waybel_0(A_979,B_980,C_978)
      | r1_waybel_0(A_979,B_980,B_977)
      | ~ m1_subset_1('#skF_2'(A_979,B_980,C_978),u1_struct_0(B_980))
      | ~ l1_waybel_0(B_980,A_979)
      | v2_struct_0(B_980)
      | ~ l1_struct_0(A_979)
      | v2_struct_0(A_979) ) ),
    inference(resolution,[status(thm)],[c_5147,c_2958])).

tff(c_5196,plain,(
    ! [C_981,C_982,A_983,B_984] :
      ( v1_xboole_0(C_981)
      | ~ r1_tarski(C_982,C_981)
      | ~ r1_waybel_0(A_983,B_984,C_982)
      | r1_waybel_0(A_983,B_984,C_981)
      | ~ m1_subset_1('#skF_2'(A_983,B_984,C_982),u1_struct_0(B_984))
      | ~ l1_waybel_0(B_984,A_983)
      | v2_struct_0(B_984)
      | ~ l1_struct_0(A_983)
      | v2_struct_0(A_983) ) ),
    inference(resolution,[status(thm)],[c_10,c_5190])).

tff(c_5226,plain,(
    ! [A_983,B_984] :
      ( v1_xboole_0('#skF_9')
      | ~ r1_waybel_0(A_983,B_984,'#skF_8')
      | r1_waybel_0(A_983,B_984,'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_983,B_984,'#skF_8'),u1_struct_0(B_984))
      | ~ l1_waybel_0(B_984,A_983)
      | v2_struct_0(B_984)
      | ~ l1_struct_0(A_983)
      | v2_struct_0(A_983) ) ),
    inference(resolution,[status(thm)],[c_34,c_5196])).

tff(c_5244,plain,(
    ! [A_985,B_986] :
      ( ~ r1_waybel_0(A_985,B_986,'#skF_8')
      | r1_waybel_0(A_985,B_986,'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_985,B_986,'#skF_8'),u1_struct_0(B_986))
      | ~ l1_waybel_0(B_986,A_985)
      | v2_struct_0(B_986)
      | ~ l1_struct_0(A_985)
      | v2_struct_0(A_985) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2695,c_5226])).

tff(c_5250,plain,(
    ! [A_987,B_988] :
      ( r1_waybel_0(A_987,B_988,'#skF_9')
      | ~ r1_waybel_0(A_987,B_988,'#skF_8')
      | ~ l1_waybel_0(B_988,A_987)
      | v2_struct_0(B_988)
      | ~ l1_struct_0(A_987)
      | v2_struct_0(A_987) ) ),
    inference(resolution,[status(thm)],[c_4,c_5244])).

tff(c_2646,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5253,plain,
    ( ~ r1_waybel_0('#skF_6','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5250,c_2646])).

tff(c_5256,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_2649,c_5253])).

tff(c_5258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_5256])).

tff(c_5260,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2694])).

tff(c_5451,plain,(
    ! [A_1044,B_1045,C_1046,D_1047] :
      ( r2_hidden(k2_waybel_0(A_1044,B_1045,'#skF_4'(A_1044,B_1045,C_1046,D_1047)),C_1046)
      | ~ m1_subset_1(D_1047,u1_struct_0(B_1045))
      | ~ r2_waybel_0(A_1044,B_1045,C_1046)
      | ~ l1_waybel_0(B_1045,A_1044)
      | v2_struct_0(B_1045)
      | ~ l1_struct_0(A_1044)
      | v2_struct_0(A_1044) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2657,plain,(
    ! [B_112,A_575,A_111] :
      ( ~ v1_xboole_0(B_112)
      | ~ r2_hidden(A_575,A_111)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_2651])).

tff(c_5538,plain,(
    ! [A_1061,D_1062,C_1060,B_1063,B_1059] :
      ( ~ v1_xboole_0(B_1063)
      | ~ r1_tarski(C_1060,B_1063)
      | ~ m1_subset_1(D_1062,u1_struct_0(B_1059))
      | ~ r2_waybel_0(A_1061,B_1059,C_1060)
      | ~ l1_waybel_0(B_1059,A_1061)
      | v2_struct_0(B_1059)
      | ~ l1_struct_0(A_1061)
      | v2_struct_0(A_1061) ) ),
    inference(resolution,[status(thm)],[c_5451,c_2657])).

tff(c_5548,plain,(
    ! [D_1062,B_1059,A_1061] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ m1_subset_1(D_1062,u1_struct_0(B_1059))
      | ~ r2_waybel_0(A_1061,B_1059,'#skF_8')
      | ~ l1_waybel_0(B_1059,A_1061)
      | v2_struct_0(B_1059)
      | ~ l1_struct_0(A_1061)
      | v2_struct_0(A_1061) ) ),
    inference(resolution,[status(thm)],[c_34,c_5538])).

tff(c_5556,plain,(
    ! [D_1064,B_1065,A_1066] :
      ( ~ m1_subset_1(D_1064,u1_struct_0(B_1065))
      | ~ r2_waybel_0(A_1066,B_1065,'#skF_8')
      | ~ l1_waybel_0(B_1065,A_1066)
      | v2_struct_0(B_1065)
      | ~ l1_struct_0(A_1066)
      | v2_struct_0(A_1066) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_5548])).

tff(c_5584,plain,(
    ! [A_1067,B_1068] :
      ( ~ r2_waybel_0(A_1067,B_1068,'#skF_8')
      | ~ l1_waybel_0(B_1068,A_1067)
      | v2_struct_0(B_1068)
      | ~ l1_struct_0(A_1067)
      | v2_struct_0(A_1067) ) ),
    inference(resolution,[status(thm)],[c_22,c_5556])).

tff(c_5587,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_5584])).

tff(c_5590,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_5587])).

tff(c_5592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_5590])).

tff(c_5593,plain,(
    r1_waybel_0('#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5598,plain,(
    ! [C_1071,B_1072,A_1073] :
      ( ~ v1_xboole_0(C_1071)
      | ~ m1_subset_1(B_1072,k1_zfmisc_1(C_1071))
      | ~ r2_hidden(A_1073,B_1072) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5620,plain,(
    ! [B_1079,A_1080,A_1081] :
      ( ~ v1_xboole_0(B_1079)
      | ~ r2_hidden(A_1080,A_1081)
      | ~ r1_tarski(A_1081,B_1079) ) ),
    inference(resolution,[status(thm)],[c_28,c_5598])).

tff(c_5634,plain,(
    ! [B_1087,B_1088,A_1089] :
      ( ~ v1_xboole_0(B_1087)
      | ~ r1_tarski(B_1088,B_1087)
      | v1_xboole_0(B_1088)
      | ~ m1_subset_1(A_1089,B_1088) ) ),
    inference(resolution,[status(thm)],[c_24,c_5620])).

tff(c_5640,plain,(
    ! [A_1089] :
      ( ~ v1_xboole_0('#skF_9')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_1089,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_5634])).

tff(c_5641,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5640])).

tff(c_5984,plain,(
    ! [A_1172,B_1173,E_1174,C_1175] :
      ( r2_hidden(k2_waybel_0(A_1172,B_1173,E_1174),C_1175)
      | ~ r1_orders_2(B_1173,'#skF_2'(A_1172,B_1173,C_1175),E_1174)
      | ~ m1_subset_1(E_1174,u1_struct_0(B_1173))
      | ~ r1_waybel_0(A_1172,B_1173,C_1175)
      | ~ l1_waybel_0(B_1173,A_1172)
      | v2_struct_0(B_1173)
      | ~ l1_struct_0(A_1172)
      | v2_struct_0(A_1172) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6165,plain,(
    ! [B_1210,C_1208,C_1207,A_1211,A_1209] :
      ( r2_hidden(k2_waybel_0(A_1209,B_1210,'#skF_1'(A_1211,B_1210,C_1207,'#skF_2'(A_1209,B_1210,C_1208))),C_1208)
      | ~ m1_subset_1('#skF_1'(A_1211,B_1210,C_1207,'#skF_2'(A_1209,B_1210,C_1208)),u1_struct_0(B_1210))
      | ~ r1_waybel_0(A_1209,B_1210,C_1208)
      | ~ l1_waybel_0(B_1210,A_1209)
      | ~ l1_struct_0(A_1209)
      | v2_struct_0(A_1209)
      | r1_waybel_0(A_1211,B_1210,C_1207)
      | ~ m1_subset_1('#skF_2'(A_1209,B_1210,C_1208),u1_struct_0(B_1210))
      | ~ l1_waybel_0(B_1210,A_1211)
      | v2_struct_0(B_1210)
      | ~ l1_struct_0(A_1211)
      | v2_struct_0(A_1211) ) ),
    inference(resolution,[status(thm)],[c_8,c_5984])).

tff(c_5612,plain,(
    ! [A_1076,C_1077,B_1078] :
      ( m1_subset_1(A_1076,C_1077)
      | ~ m1_subset_1(B_1078,k1_zfmisc_1(C_1077))
      | ~ r2_hidden(A_1076,B_1078) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5618,plain,(
    ! [A_1076,B_112,A_111] :
      ( m1_subset_1(A_1076,B_112)
      | ~ r2_hidden(A_1076,A_111)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_5612])).

tff(c_7979,plain,(
    ! [A_1456,C_1453,A_1458,B_1457,B_1454,C_1455] :
      ( m1_subset_1(k2_waybel_0(A_1456,B_1454,'#skF_1'(A_1458,B_1454,C_1455,'#skF_2'(A_1456,B_1454,C_1453))),B_1457)
      | ~ r1_tarski(C_1453,B_1457)
      | ~ m1_subset_1('#skF_1'(A_1458,B_1454,C_1455,'#skF_2'(A_1456,B_1454,C_1453)),u1_struct_0(B_1454))
      | ~ r1_waybel_0(A_1456,B_1454,C_1453)
      | ~ l1_waybel_0(B_1454,A_1456)
      | ~ l1_struct_0(A_1456)
      | v2_struct_0(A_1456)
      | r1_waybel_0(A_1458,B_1454,C_1455)
      | ~ m1_subset_1('#skF_2'(A_1456,B_1454,C_1453),u1_struct_0(B_1454))
      | ~ l1_waybel_0(B_1454,A_1458)
      | v2_struct_0(B_1454)
      | ~ l1_struct_0(A_1458)
      | v2_struct_0(A_1458) ) ),
    inference(resolution,[status(thm)],[c_6165,c_5618])).

tff(c_5801,plain,(
    ! [A_1137,B_1138,C_1139,D_1140] :
      ( ~ r2_hidden(k2_waybel_0(A_1137,B_1138,'#skF_1'(A_1137,B_1138,C_1139,D_1140)),C_1139)
      | r1_waybel_0(A_1137,B_1138,C_1139)
      | ~ m1_subset_1(D_1140,u1_struct_0(B_1138))
      | ~ l1_waybel_0(B_1138,A_1137)
      | v2_struct_0(B_1138)
      | ~ l1_struct_0(A_1137)
      | v2_struct_0(A_1137) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5806,plain,(
    ! [A_1137,B_1138,B_110,D_1140] :
      ( r1_waybel_0(A_1137,B_1138,B_110)
      | ~ m1_subset_1(D_1140,u1_struct_0(B_1138))
      | ~ l1_waybel_0(B_1138,A_1137)
      | v2_struct_0(B_1138)
      | ~ l1_struct_0(A_1137)
      | v2_struct_0(A_1137)
      | v1_xboole_0(B_110)
      | ~ m1_subset_1(k2_waybel_0(A_1137,B_1138,'#skF_1'(A_1137,B_1138,B_110,D_1140)),B_110) ) ),
    inference(resolution,[status(thm)],[c_24,c_5801])).

tff(c_8018,plain,(
    ! [B_1459,C_1460,A_1461,B_1462] :
      ( v1_xboole_0(B_1459)
      | ~ r1_tarski(C_1460,B_1459)
      | ~ m1_subset_1('#skF_1'(A_1461,B_1462,B_1459,'#skF_2'(A_1461,B_1462,C_1460)),u1_struct_0(B_1462))
      | ~ r1_waybel_0(A_1461,B_1462,C_1460)
      | r1_waybel_0(A_1461,B_1462,B_1459)
      | ~ m1_subset_1('#skF_2'(A_1461,B_1462,C_1460),u1_struct_0(B_1462))
      | ~ l1_waybel_0(B_1462,A_1461)
      | v2_struct_0(B_1462)
      | ~ l1_struct_0(A_1461)
      | v2_struct_0(A_1461) ) ),
    inference(resolution,[status(thm)],[c_7979,c_5806])).

tff(c_8024,plain,(
    ! [C_1463,C_1464,A_1465,B_1466] :
      ( v1_xboole_0(C_1463)
      | ~ r1_tarski(C_1464,C_1463)
      | ~ r1_waybel_0(A_1465,B_1466,C_1464)
      | r1_waybel_0(A_1465,B_1466,C_1463)
      | ~ m1_subset_1('#skF_2'(A_1465,B_1466,C_1464),u1_struct_0(B_1466))
      | ~ l1_waybel_0(B_1466,A_1465)
      | v2_struct_0(B_1466)
      | ~ l1_struct_0(A_1465)
      | v2_struct_0(A_1465) ) ),
    inference(resolution,[status(thm)],[c_10,c_8018])).

tff(c_8052,plain,(
    ! [A_1465,B_1466] :
      ( v1_xboole_0('#skF_9')
      | ~ r1_waybel_0(A_1465,B_1466,'#skF_8')
      | r1_waybel_0(A_1465,B_1466,'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_1465,B_1466,'#skF_8'),u1_struct_0(B_1466))
      | ~ l1_waybel_0(B_1466,A_1465)
      | v2_struct_0(B_1466)
      | ~ l1_struct_0(A_1465)
      | v2_struct_0(A_1465) ) ),
    inference(resolution,[status(thm)],[c_34,c_8024])).

tff(c_8069,plain,(
    ! [A_1467,B_1468] :
      ( ~ r1_waybel_0(A_1467,B_1468,'#skF_8')
      | r1_waybel_0(A_1467,B_1468,'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_1467,B_1468,'#skF_8'),u1_struct_0(B_1468))
      | ~ l1_waybel_0(B_1468,A_1467)
      | v2_struct_0(B_1468)
      | ~ l1_struct_0(A_1467)
      | v2_struct_0(A_1467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5641,c_8052])).

tff(c_8075,plain,(
    ! [A_1469,B_1470] :
      ( r1_waybel_0(A_1469,B_1470,'#skF_9')
      | ~ r1_waybel_0(A_1469,B_1470,'#skF_8')
      | ~ l1_waybel_0(B_1470,A_1469)
      | v2_struct_0(B_1470)
      | ~ l1_struct_0(A_1469)
      | v2_struct_0(A_1469) ) ),
    inference(resolution,[status(thm)],[c_4,c_8069])).

tff(c_5594,plain,(
    ~ r2_waybel_0('#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( ~ r1_waybel_0('#skF_6','#skF_7','#skF_9')
    | r2_waybel_0('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5595,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_5594,c_48])).

tff(c_8078,plain,
    ( ~ r1_waybel_0('#skF_6','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_8075,c_5595])).

tff(c_8081,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_5593,c_8078])).

tff(c_8083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_8081])).

tff(c_8085,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_5640])).

tff(c_8411,plain,(
    ! [A_1554,B_1555,E_1556,C_1557] :
      ( r2_hidden(k2_waybel_0(A_1554,B_1555,E_1556),C_1557)
      | ~ r1_orders_2(B_1555,'#skF_2'(A_1554,B_1555,C_1557),E_1556)
      | ~ m1_subset_1(E_1556,u1_struct_0(B_1555))
      | ~ r1_waybel_0(A_1554,B_1555,C_1557)
      | ~ l1_waybel_0(B_1555,A_1554)
      | v2_struct_0(B_1555)
      | ~ l1_struct_0(A_1554)
      | v2_struct_0(A_1554) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8905,plain,(
    ! [A_1628,B_1627,C_1624,C_1626,A_1625] :
      ( r2_hidden(k2_waybel_0(A_1625,B_1627,'#skF_1'(A_1628,B_1627,C_1626,'#skF_2'(A_1625,B_1627,C_1624))),C_1624)
      | ~ m1_subset_1('#skF_1'(A_1628,B_1627,C_1626,'#skF_2'(A_1625,B_1627,C_1624)),u1_struct_0(B_1627))
      | ~ r1_waybel_0(A_1625,B_1627,C_1624)
      | ~ l1_waybel_0(B_1627,A_1625)
      | ~ l1_struct_0(A_1625)
      | v2_struct_0(A_1625)
      | r1_waybel_0(A_1628,B_1627,C_1626)
      | ~ m1_subset_1('#skF_2'(A_1625,B_1627,C_1624),u1_struct_0(B_1627))
      | ~ l1_waybel_0(B_1627,A_1628)
      | v2_struct_0(B_1627)
      | ~ l1_struct_0(A_1628)
      | v2_struct_0(A_1628) ) ),
    inference(resolution,[status(thm)],[c_8,c_8411])).

tff(c_5604,plain,(
    ! [B_112,A_1073,A_111] :
      ( ~ v1_xboole_0(B_112)
      | ~ r2_hidden(A_1073,A_111)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_5598])).

tff(c_9293,plain,(
    ! [A_1675,C_1676,B_1677,B_1672,A_1673,C_1674] :
      ( ~ v1_xboole_0(B_1677)
      | ~ r1_tarski(C_1676,B_1677)
      | ~ m1_subset_1('#skF_1'(A_1673,B_1672,C_1674,'#skF_2'(A_1675,B_1672,C_1676)),u1_struct_0(B_1672))
      | ~ r1_waybel_0(A_1675,B_1672,C_1676)
      | ~ l1_waybel_0(B_1672,A_1675)
      | ~ l1_struct_0(A_1675)
      | v2_struct_0(A_1675)
      | r1_waybel_0(A_1673,B_1672,C_1674)
      | ~ m1_subset_1('#skF_2'(A_1675,B_1672,C_1676),u1_struct_0(B_1672))
      | ~ l1_waybel_0(B_1672,A_1673)
      | v2_struct_0(B_1672)
      | ~ l1_struct_0(A_1673)
      | v2_struct_0(A_1673) ) ),
    inference(resolution,[status(thm)],[c_8905,c_5604])).

tff(c_9317,plain,(
    ! [A_1673,B_1672,C_1674,A_1675] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ m1_subset_1('#skF_1'(A_1673,B_1672,C_1674,'#skF_2'(A_1675,B_1672,'#skF_8')),u1_struct_0(B_1672))
      | ~ r1_waybel_0(A_1675,B_1672,'#skF_8')
      | ~ l1_waybel_0(B_1672,A_1675)
      | ~ l1_struct_0(A_1675)
      | v2_struct_0(A_1675)
      | r1_waybel_0(A_1673,B_1672,C_1674)
      | ~ m1_subset_1('#skF_2'(A_1675,B_1672,'#skF_8'),u1_struct_0(B_1672))
      | ~ l1_waybel_0(B_1672,A_1673)
      | v2_struct_0(B_1672)
      | ~ l1_struct_0(A_1673)
      | v2_struct_0(A_1673) ) ),
    inference(resolution,[status(thm)],[c_34,c_9293])).

tff(c_9389,plain,(
    ! [A_1685,B_1686,C_1687,A_1688] :
      ( ~ m1_subset_1('#skF_1'(A_1685,B_1686,C_1687,'#skF_2'(A_1688,B_1686,'#skF_8')),u1_struct_0(B_1686))
      | ~ r1_waybel_0(A_1688,B_1686,'#skF_8')
      | ~ l1_waybel_0(B_1686,A_1688)
      | ~ l1_struct_0(A_1688)
      | v2_struct_0(A_1688)
      | r1_waybel_0(A_1685,B_1686,C_1687)
      | ~ m1_subset_1('#skF_2'(A_1688,B_1686,'#skF_8'),u1_struct_0(B_1686))
      | ~ l1_waybel_0(B_1686,A_1685)
      | v2_struct_0(B_1686)
      | ~ l1_struct_0(A_1685)
      | v2_struct_0(A_1685) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8085,c_9317])).

tff(c_9395,plain,(
    ! [A_1689,B_1690,A_1691,C_1692] :
      ( ~ r1_waybel_0(A_1689,B_1690,'#skF_8')
      | ~ l1_waybel_0(B_1690,A_1689)
      | ~ l1_struct_0(A_1689)
      | v2_struct_0(A_1689)
      | r1_waybel_0(A_1691,B_1690,C_1692)
      | ~ m1_subset_1('#skF_2'(A_1689,B_1690,'#skF_8'),u1_struct_0(B_1690))
      | ~ l1_waybel_0(B_1690,A_1691)
      | v2_struct_0(B_1690)
      | ~ l1_struct_0(A_1691)
      | v2_struct_0(A_1691) ) ),
    inference(resolution,[status(thm)],[c_10,c_9389])).

tff(c_9400,plain,(
    ! [A_1693,B_1694,C_1695,A_1696] :
      ( r1_waybel_0(A_1693,B_1694,C_1695)
      | ~ l1_waybel_0(B_1694,A_1693)
      | ~ l1_struct_0(A_1693)
      | v2_struct_0(A_1693)
      | ~ r1_waybel_0(A_1696,B_1694,'#skF_8')
      | ~ l1_waybel_0(B_1694,A_1696)
      | v2_struct_0(B_1694)
      | ~ l1_struct_0(A_1696)
      | v2_struct_0(A_1696) ) ),
    inference(resolution,[status(thm)],[c_4,c_9395])).

tff(c_9402,plain,(
    ! [A_1693,C_1695] :
      ( r1_waybel_0(A_1693,'#skF_7',C_1695)
      | ~ l1_waybel_0('#skF_7',A_1693)
      | ~ l1_struct_0(A_1693)
      | v2_struct_0(A_1693)
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5593,c_9400])).

tff(c_9405,plain,(
    ! [A_1693,C_1695] :
      ( r1_waybel_0(A_1693,'#skF_7',C_1695)
      | ~ l1_waybel_0('#skF_7',A_1693)
      | ~ l1_struct_0(A_1693)
      | v2_struct_0(A_1693)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_9402])).

tff(c_9407,plain,(
    ! [A_1697,C_1698] :
      ( r1_waybel_0(A_1697,'#skF_7',C_1698)
      | ~ l1_waybel_0('#skF_7',A_1697)
      | ~ l1_struct_0(A_1697)
      | v2_struct_0(A_1697) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_9405])).

tff(c_9413,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9407,c_5595])).

tff(c_9418,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_9413])).

tff(c_9420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_9418])).

%------------------------------------------------------------------------------
