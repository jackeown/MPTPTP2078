%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 31.99s
% Output     : CNFRefutation 32.10s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 736 expanded)
%              Number of leaves         :   41 ( 251 expanded)
%              Depth                    :   20
%              Number of atoms          :  446 (2941 expanded)
%              Number of equality atoms :   23 ( 108 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_167,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_76,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_58076,plain,(
    ! [B_1376,A_1377] :
      ( l1_pre_topc(B_1376)
      | ~ m1_pre_topc(B_1376,A_1377)
      | ~ l1_pre_topc(A_1377) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58079,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_58076])).

tff(c_58091,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_58079])).

tff(c_46,plain,(
    ! [A_49] :
      ( l1_struct_0(A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_84,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_58082,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_58076])).

tff(c_58094,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_58082])).

tff(c_80,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_57962,plain,(
    ! [B_1363,A_1364] :
      ( l1_pre_topc(B_1363)
      | ~ m1_pre_topc(B_1363,A_1364)
      | ~ l1_pre_topc(A_1364) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57974,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_57962])).

tff(c_57984,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_57974])).

tff(c_74,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_57981,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_57962])).

tff(c_57985,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_57981])).

tff(c_57999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57984,c_57985])).

tff(c_58001,plain,(
    l1_pre_topc('#skF_6') ),
    inference(splitRight,[status(thm)],[c_57981])).

tff(c_57965,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_57962])).

tff(c_57977,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_57965])).

tff(c_72,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_102,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_113,plain,(
    ! [B_100,A_101] :
      ( l1_pre_topc(B_100)
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_113])).

tff(c_128,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_116])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_113])).

tff(c_135,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_125])).

tff(c_70,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_103,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_175,plain,(
    ! [B_112,A_113] :
      ( r1_tsep_1(B_112,A_113)
      | ~ r1_tsep_1(A_113,B_112)
      | ~ l1_struct_0(B_112)
      | ~ l1_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_178,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_103,c_175])).

tff(c_179,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_182,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_182])).

tff(c_187,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_206])).

tff(c_212,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_119,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_113])).

tff(c_131,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_119])).

tff(c_97,plain,(
    ! [A_98] :
      ( u1_struct_0(A_98) = k2_struct_0(A_98)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_143,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_101])).

tff(c_139,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_128,c_101])).

tff(c_274,plain,(
    ! [A_120,B_121] :
      ( r1_tsep_1(A_120,B_121)
      | ~ r1_xboole_0(u1_struct_0(A_120),u1_struct_0(B_121))
      | ~ l1_struct_0(B_121)
      | ~ l1_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_295,plain,(
    ! [A_120] :
      ( r1_tsep_1(A_120,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_120),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_274])).

tff(c_494,plain,(
    ! [A_133] :
      ( r1_tsep_1(A_133,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_133),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_295])).

tff(c_500,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_494])).

tff(c_511,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_500])).

tff(c_556,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_511])).

tff(c_581,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_556])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_581])).

tff(c_587,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_90,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_397,plain,(
    ! [B_127,C_128,A_129] :
      ( m1_pre_topc(B_127,C_128)
      | ~ r1_tarski(u1_struct_0(B_127),u1_struct_0(C_128))
      | ~ m1_pre_topc(C_128,A_129)
      | ~ m1_pre_topc(B_127,A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_418,plain,(
    ! [B_130,A_131] :
      ( m1_pre_topc(B_130,B_130)
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_426,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_418])).

tff(c_438,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_426])).

tff(c_750,plain,(
    ! [A_151,B_152,C_153] :
      ( m1_pre_topc(k1_tsep_1(A_151,B_152,C_153),A_151)
      | ~ m1_pre_topc(C_153,A_151)
      | v2_struct_0(C_153)
      | ~ m1_pre_topc(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    ! [B_52,A_50] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_760,plain,(
    ! [A_151,B_152,C_153] :
      ( l1_pre_topc(k1_tsep_1(A_151,B_152,C_153))
      | ~ m1_pre_topc(C_153,A_151)
      | v2_struct_0(C_153)
      | ~ m1_pre_topc(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_750,c_48])).

tff(c_58,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_pre_topc(k1_tsep_1(A_71,B_72,C_73),A_71)
      | ~ m1_pre_topc(C_73,A_71)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_36,plain,(
    ! [B_31,A_9] :
      ( r1_tarski(k2_struct_0(B_31),k2_struct_0(A_9))
      | ~ m1_pre_topc(B_31,A_9)
      | ~ l1_pre_topc(B_31)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1416,plain,(
    ! [A_212,B_213,C_214] :
      ( l1_pre_topc(k1_tsep_1(A_212,B_213,C_214))
      | ~ m1_pre_topc(C_214,A_212)
      | v2_struct_0(C_214)
      | ~ m1_pre_topc(B_213,A_212)
      | v2_struct_0(B_213)
      | ~ l1_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_750,c_48])).

tff(c_1420,plain,(
    ! [A_212,B_213,C_214] :
      ( u1_struct_0(k1_tsep_1(A_212,B_213,C_214)) = k2_struct_0(k1_tsep_1(A_212,B_213,C_214))
      | ~ m1_pre_topc(C_214,A_212)
      | v2_struct_0(C_214)
      | ~ m1_pre_topc(B_213,A_212)
      | v2_struct_0(B_213)
      | ~ l1_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_1416,c_101])).

tff(c_188,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_211,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_147,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_135,c_101])).

tff(c_223,plain,(
    ! [A_117,B_118] :
      ( r1_xboole_0(u1_struct_0(A_117),u1_struct_0(B_118))
      | ~ r1_tsep_1(A_117,B_118)
      | ~ l1_struct_0(B_118)
      | ~ l1_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_238,plain,(
    ! [B_118] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_118))
      | ~ r1_tsep_1('#skF_7',B_118)
      | ~ l1_struct_0(B_118)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_223])).

tff(c_349,plain,(
    ! [B_123] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_123))
      | ~ r1_tsep_1('#skF_7',B_123)
      | ~ l1_struct_0(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_238])).

tff(c_355,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_349])).

tff(c_363,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_211,c_355])).

tff(c_60,plain,(
    ! [A_71,B_72,C_73] :
      ( v1_pre_topc(k1_tsep_1(A_71,B_72,C_73))
      | ~ m1_pre_topc(C_73,A_71)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1890,plain,(
    ! [A_305,B_306,C_307] :
      ( u1_struct_0(k1_tsep_1(A_305,B_306,C_307)) = k2_xboole_0(u1_struct_0(B_306),u1_struct_0(C_307))
      | ~ m1_pre_topc(k1_tsep_1(A_305,B_306,C_307),A_305)
      | ~ v1_pre_topc(k1_tsep_1(A_305,B_306,C_307))
      | v2_struct_0(k1_tsep_1(A_305,B_306,C_307))
      | ~ m1_pre_topc(C_307,A_305)
      | v2_struct_0(C_307)
      | ~ m1_pre_topc(B_306,A_305)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2142,plain,(
    ! [A_348,B_349,C_350] :
      ( u1_struct_0(k1_tsep_1(A_348,B_349,C_350)) = k2_xboole_0(u1_struct_0(B_349),u1_struct_0(C_350))
      | ~ v1_pre_topc(k1_tsep_1(A_348,B_349,C_350))
      | v2_struct_0(k1_tsep_1(A_348,B_349,C_350))
      | ~ m1_pre_topc(C_350,A_348)
      | v2_struct_0(C_350)
      | ~ m1_pre_topc(B_349,A_348)
      | v2_struct_0(B_349)
      | ~ l1_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(resolution,[status(thm)],[c_58,c_1890])).

tff(c_62,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ v2_struct_0(k1_tsep_1(A_71,B_72,C_73))
      | ~ m1_pre_topc(C_73,A_71)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2454,plain,(
    ! [A_351,B_352,C_353] :
      ( u1_struct_0(k1_tsep_1(A_351,B_352,C_353)) = k2_xboole_0(u1_struct_0(B_352),u1_struct_0(C_353))
      | ~ v1_pre_topc(k1_tsep_1(A_351,B_352,C_353))
      | ~ m1_pre_topc(C_353,A_351)
      | v2_struct_0(C_353)
      | ~ m1_pre_topc(B_352,A_351)
      | v2_struct_0(B_352)
      | ~ l1_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_2142,c_62])).

tff(c_2458,plain,(
    ! [A_354,B_355,C_356] :
      ( u1_struct_0(k1_tsep_1(A_354,B_355,C_356)) = k2_xboole_0(u1_struct_0(B_355),u1_struct_0(C_356))
      | ~ m1_pre_topc(C_356,A_354)
      | v2_struct_0(C_356)
      | ~ m1_pre_topc(B_355,A_354)
      | v2_struct_0(B_355)
      | ~ l1_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_60,c_2454])).

tff(c_2740,plain,(
    ! [A_354,C_356] :
      ( u1_struct_0(k1_tsep_1(A_354,'#skF_6',C_356)) = k2_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(C_356))
      | ~ m1_pre_topc(C_356,A_354)
      | v2_struct_0(C_356)
      | ~ m1_pre_topc('#skF_6',A_354)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2458])).

tff(c_6296,plain,(
    ! [A_407,C_408] :
      ( u1_struct_0(k1_tsep_1(A_407,'#skF_6',C_408)) = k2_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(C_408))
      | ~ m1_pre_topc(C_408,A_407)
      | v2_struct_0(C_408)
      | ~ m1_pre_topc('#skF_6',A_407)
      | ~ l1_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2740])).

tff(c_6652,plain,(
    ! [A_407] :
      ( u1_struct_0(k1_tsep_1(A_407,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_407)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_6',A_407)
      | ~ l1_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_6296])).

tff(c_6700,plain,(
    ! [A_409] :
      ( u1_struct_0(k1_tsep_1(A_409,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_409)
      | ~ m1_pre_topc('#skF_6',A_409)
      | ~ l1_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6652])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_164])).

tff(c_6967,plain,(
    ! [A_409] :
      ( k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_6')
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(A_409,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_409)
      | ~ m1_pre_topc('#skF_6',A_409)
      | ~ l1_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6700,c_169])).

tff(c_23259,plain,(
    k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6967])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23285,plain,(
    ! [A_817] :
      ( r1_xboole_0(A_817,k2_struct_0('#skF_5'))
      | ~ r1_xboole_0(A_817,k2_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23259,c_10])).

tff(c_292,plain,(
    ! [B_121] :
      ( r1_tsep_1('#skF_7',B_121)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_121))
      | ~ l1_struct_0(B_121)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_274])).

tff(c_649,plain,(
    ! [B_146] :
      ( r1_tsep_1('#skF_7',B_146)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_146))
      | ~ l1_struct_0(B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_292])).

tff(c_655,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_649])).

tff(c_667,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_655])).

tff(c_721,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_23300,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_23285,c_721])).

tff(c_23308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_23300])).

tff(c_23350,plain,(
    ! [A_819] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(A_819,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_819)
      | ~ m1_pre_topc('#skF_6',A_819)
      | ~ l1_pre_topc(A_819)
      | v2_struct_0(A_819) ) ),
    inference(splitRight,[status(thm)],[c_6967])).

tff(c_23377,plain,(
    ! [A_212] :
      ( ~ r1_tarski(k2_struct_0(k1_tsep_1(A_212,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_212)
      | ~ m1_pre_topc('#skF_6',A_212)
      | ~ l1_pre_topc(A_212)
      | v2_struct_0(A_212)
      | ~ m1_pre_topc('#skF_5',A_212)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_6',A_212)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_23350])).

tff(c_57754,plain,(
    ! [A_1359] :
      ( ~ r1_tarski(k2_struct_0(k1_tsep_1(A_1359,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_1359)
      | ~ m1_pre_topc('#skF_6',A_1359)
      | ~ l1_pre_topc(A_1359)
      | v2_struct_0(A_1359)
      | ~ m1_pre_topc('#skF_5',A_1359)
      | ~ m1_pre_topc('#skF_6',A_1359)
      | ~ l1_pre_topc(A_1359)
      | v2_struct_0(A_1359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86,c_23377])).

tff(c_57764,plain,(
    ! [A_1359] :
      ( ~ m1_pre_topc('#skF_5',A_1359)
      | ~ m1_pre_topc('#skF_6',A_1359)
      | ~ l1_pre_topc(A_1359)
      | v2_struct_0(A_1359)
      | ~ m1_pre_topc(k1_tsep_1(A_1359,'#skF_6','#skF_5'),'#skF_6')
      | ~ l1_pre_topc(k1_tsep_1(A_1359,'#skF_6','#skF_5'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_57754])).

tff(c_57925,plain,(
    ! [A_1361] :
      ( ~ m1_pre_topc('#skF_5',A_1361)
      | ~ m1_pre_topc('#skF_6',A_1361)
      | ~ l1_pre_topc(A_1361)
      | v2_struct_0(A_1361)
      | ~ m1_pre_topc(k1_tsep_1(A_1361,'#skF_6','#skF_5'),'#skF_6')
      | ~ l1_pre_topc(k1_tsep_1(A_1361,'#skF_6','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_57764])).

tff(c_57929,plain,
    ( ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_57925])).

tff(c_57932,plain,
    ( ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_6','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_438,c_74,c_57929])).

tff(c_57933,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86,c_57932])).

tff(c_57936,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_760,c_57933])).

tff(c_57939,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_438,c_74,c_57936])).

tff(c_57941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86,c_57939])).

tff(c_57942,plain,(
    r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_64,plain,(
    ! [B_75,A_74] :
      ( r1_tsep_1(B_75,A_74)
      | ~ r1_tsep_1(A_74,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_57945,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_57942,c_64])).

tff(c_57948,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_587,c_57945])).

tff(c_57950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_57948])).

tff(c_57952,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_57951,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_58040,plain,(
    ! [B_1373,A_1374] :
      ( r1_tsep_1(B_1373,A_1374)
      | ~ r1_tsep_1(A_1374,B_1373)
      | ~ l1_struct_0(B_1373)
      | ~ l1_struct_0(A_1374) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_58042,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_57951,c_58040])).

tff(c_58045,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_57952,c_58042])).

tff(c_58046,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58045])).

tff(c_58049,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_58046])).

tff(c_58053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57977,c_58049])).

tff(c_58054,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_58045])).

tff(c_58063,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_58054])).

tff(c_58067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58001,c_58063])).

tff(c_58068,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_58069,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_58142,plain,(
    ! [B_1388,A_1389] :
      ( r1_tsep_1(B_1388,A_1389)
      | ~ r1_tsep_1(A_1389,B_1388)
      | ~ l1_struct_0(B_1388)
      | ~ l1_struct_0(A_1389) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_58146,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58069,c_58142])).

tff(c_58150,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58068,c_58146])).

tff(c_58151,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58150])).

tff(c_58154,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_58151])).

tff(c_58158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58094,c_58154])).

tff(c_58159,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_58150])).

tff(c_58163,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_58159])).

tff(c_58167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58091,c_58163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.99/20.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.99/20.87  
% 31.99/20.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.10/20.87  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 32.10/20.87  
% 32.10/20.87  %Foreground sorts:
% 32.10/20.87  
% 32.10/20.87  
% 32.10/20.87  %Background operators:
% 32.10/20.87  
% 32.10/20.87  
% 32.10/20.87  %Foreground operators:
% 32.10/20.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 32.10/20.87  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 32.10/20.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 32.10/20.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 32.10/20.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.10/20.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.10/20.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 32.10/20.87  tff('#skF_7', type, '#skF_7': $i).
% 32.10/20.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 32.10/20.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.10/20.87  tff('#skF_5', type, '#skF_5': $i).
% 32.10/20.87  tff('#skF_6', type, '#skF_6': $i).
% 32.10/20.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 32.10/20.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 32.10/20.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 32.10/20.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 32.10/20.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.10/20.87  tff('#skF_4', type, '#skF_4': $i).
% 32.10/20.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.10/20.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 32.10/20.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 32.10/20.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 32.10/20.87  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 32.10/20.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.10/20.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 32.10/20.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 32.10/20.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 32.10/20.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 32.10/20.87  
% 32.10/20.90  tff(f_205, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 32.10/20.90  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 32.10/20.90  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 32.10/20.90  tff(f_153, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 32.10/20.90  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 32.10/20.90  tff(f_123, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 32.10/20.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.10/20.90  tff(f_167, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 32.10/20.90  tff(f_145, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 32.10/20.90  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 32.10/20.90  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 32.10/20.90  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 32.10/20.90  tff(f_47, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 32.10/20.90  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_76, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_58076, plain, (![B_1376, A_1377]: (l1_pre_topc(B_1376) | ~m1_pre_topc(B_1376, A_1377) | ~l1_pre_topc(A_1377))), inference(cnfTransformation, [status(thm)], [f_85])).
% 32.10/20.90  tff(c_58079, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_58076])).
% 32.10/20.90  tff(c_58091, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_58079])).
% 32.10/20.90  tff(c_46, plain, (![A_49]: (l1_struct_0(A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 32.10/20.90  tff(c_84, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_58082, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_84, c_58076])).
% 32.10/20.90  tff(c_58094, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_58082])).
% 32.10/20.90  tff(c_80, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_57962, plain, (![B_1363, A_1364]: (l1_pre_topc(B_1363) | ~m1_pre_topc(B_1363, A_1364) | ~l1_pre_topc(A_1364))), inference(cnfTransformation, [status(thm)], [f_85])).
% 32.10/20.90  tff(c_57974, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_80, c_57962])).
% 32.10/20.90  tff(c_57984, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_57974])).
% 32.10/20.90  tff(c_74, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_57981, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_74, c_57962])).
% 32.10/20.90  tff(c_57985, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_57981])).
% 32.10/20.90  tff(c_57999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57984, c_57985])).
% 32.10/20.90  tff(c_58001, plain, (l1_pre_topc('#skF_6')), inference(splitRight, [status(thm)], [c_57981])).
% 32.10/20.90  tff(c_57965, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_57962])).
% 32.10/20.90  tff(c_57977, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_57965])).
% 32.10/20.90  tff(c_72, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_102, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_72])).
% 32.10/20.90  tff(c_113, plain, (![B_100, A_101]: (l1_pre_topc(B_100) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_85])).
% 32.10/20.90  tff(c_116, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_113])).
% 32.10/20.90  tff(c_128, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_116])).
% 32.10/20.90  tff(c_125, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_80, c_113])).
% 32.10/20.90  tff(c_135, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_125])).
% 32.10/20.90  tff(c_70, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_103, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 32.10/20.90  tff(c_175, plain, (![B_112, A_113]: (r1_tsep_1(B_112, A_113) | ~r1_tsep_1(A_113, B_112) | ~l1_struct_0(B_112) | ~l1_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_153])).
% 32.10/20.90  tff(c_178, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_103, c_175])).
% 32.10/20.90  tff(c_179, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_178])).
% 32.10/20.90  tff(c_182, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_46, c_179])).
% 32.10/20.90  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_182])).
% 32.10/20.90  tff(c_187, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_178])).
% 32.10/20.90  tff(c_203, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_187])).
% 32.10/20.90  tff(c_206, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_203])).
% 32.10/20.90  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_206])).
% 32.10/20.90  tff(c_212, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_187])).
% 32.10/20.90  tff(c_119, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_84, c_113])).
% 32.10/20.90  tff(c_131, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_119])).
% 32.10/20.90  tff(c_97, plain, (![A_98]: (u1_struct_0(A_98)=k2_struct_0(A_98) | ~l1_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.10/20.90  tff(c_101, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_46, c_97])).
% 32.10/20.90  tff(c_143, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_131, c_101])).
% 32.10/20.90  tff(c_139, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_128, c_101])).
% 32.10/20.90  tff(c_274, plain, (![A_120, B_121]: (r1_tsep_1(A_120, B_121) | ~r1_xboole_0(u1_struct_0(A_120), u1_struct_0(B_121)) | ~l1_struct_0(B_121) | ~l1_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_123])).
% 32.10/20.90  tff(c_295, plain, (![A_120]: (r1_tsep_1(A_120, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_120), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_120))), inference(superposition, [status(thm), theory('equality')], [c_139, c_274])).
% 32.10/20.90  tff(c_494, plain, (![A_133]: (r1_tsep_1(A_133, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_133), k2_struct_0('#skF_7')) | ~l1_struct_0(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_295])).
% 32.10/20.90  tff(c_500, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_143, c_494])).
% 32.10/20.90  tff(c_511, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_102, c_500])).
% 32.10/20.90  tff(c_556, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_511])).
% 32.10/20.90  tff(c_581, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_556])).
% 32.10/20.90  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_581])).
% 32.10/20.90  tff(c_587, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_511])).
% 32.10/20.90  tff(c_82, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_86, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_90, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 32.10/20.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.10/20.90  tff(c_397, plain, (![B_127, C_128, A_129]: (m1_pre_topc(B_127, C_128) | ~r1_tarski(u1_struct_0(B_127), u1_struct_0(C_128)) | ~m1_pre_topc(C_128, A_129) | ~m1_pre_topc(B_127, A_129) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_167])).
% 32.10/20.90  tff(c_418, plain, (![B_130, A_131]: (m1_pre_topc(B_130, B_130) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131))), inference(resolution, [status(thm)], [c_6, c_397])).
% 32.10/20.90  tff(c_426, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_80, c_418])).
% 32.10/20.90  tff(c_438, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_426])).
% 32.10/20.90  tff(c_750, plain, (![A_151, B_152, C_153]: (m1_pre_topc(k1_tsep_1(A_151, B_152, C_153), A_151) | ~m1_pre_topc(C_153, A_151) | v2_struct_0(C_153) | ~m1_pre_topc(B_152, A_151) | v2_struct_0(B_152) | ~l1_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_145])).
% 32.10/20.90  tff(c_48, plain, (![B_52, A_50]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 32.10/20.90  tff(c_760, plain, (![A_151, B_152, C_153]: (l1_pre_topc(k1_tsep_1(A_151, B_152, C_153)) | ~m1_pre_topc(C_153, A_151) | v2_struct_0(C_153) | ~m1_pre_topc(B_152, A_151) | v2_struct_0(B_152) | ~l1_pre_topc(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_750, c_48])).
% 32.10/20.90  tff(c_58, plain, (![A_71, B_72, C_73]: (m1_pre_topc(k1_tsep_1(A_71, B_72, C_73), A_71) | ~m1_pre_topc(C_73, A_71) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_71) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_145])).
% 32.10/20.90  tff(c_36, plain, (![B_31, A_9]: (r1_tarski(k2_struct_0(B_31), k2_struct_0(A_9)) | ~m1_pre_topc(B_31, A_9) | ~l1_pre_topc(B_31) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_74])).
% 32.10/20.90  tff(c_1416, plain, (![A_212, B_213, C_214]: (l1_pre_topc(k1_tsep_1(A_212, B_213, C_214)) | ~m1_pre_topc(C_214, A_212) | v2_struct_0(C_214) | ~m1_pre_topc(B_213, A_212) | v2_struct_0(B_213) | ~l1_pre_topc(A_212) | v2_struct_0(A_212))), inference(resolution, [status(thm)], [c_750, c_48])).
% 32.10/20.90  tff(c_1420, plain, (![A_212, B_213, C_214]: (u1_struct_0(k1_tsep_1(A_212, B_213, C_214))=k2_struct_0(k1_tsep_1(A_212, B_213, C_214)) | ~m1_pre_topc(C_214, A_212) | v2_struct_0(C_214) | ~m1_pre_topc(B_213, A_212) | v2_struct_0(B_213) | ~l1_pre_topc(A_212) | v2_struct_0(A_212))), inference(resolution, [status(thm)], [c_1416, c_101])).
% 32.10/20.90  tff(c_188, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_178])).
% 32.10/20.90  tff(c_211, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_187])).
% 32.10/20.90  tff(c_147, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_135, c_101])).
% 32.10/20.90  tff(c_223, plain, (![A_117, B_118]: (r1_xboole_0(u1_struct_0(A_117), u1_struct_0(B_118)) | ~r1_tsep_1(A_117, B_118) | ~l1_struct_0(B_118) | ~l1_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_123])).
% 32.10/20.90  tff(c_238, plain, (![B_118]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_118)) | ~r1_tsep_1('#skF_7', B_118) | ~l1_struct_0(B_118) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_223])).
% 32.10/20.90  tff(c_349, plain, (![B_123]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_123)) | ~r1_tsep_1('#skF_7', B_123) | ~l1_struct_0(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_238])).
% 32.10/20.90  tff(c_355, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_147, c_349])).
% 32.10/20.90  tff(c_363, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_211, c_355])).
% 32.10/20.90  tff(c_60, plain, (![A_71, B_72, C_73]: (v1_pre_topc(k1_tsep_1(A_71, B_72, C_73)) | ~m1_pre_topc(C_73, A_71) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_71) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_145])).
% 32.10/20.90  tff(c_1890, plain, (![A_305, B_306, C_307]: (u1_struct_0(k1_tsep_1(A_305, B_306, C_307))=k2_xboole_0(u1_struct_0(B_306), u1_struct_0(C_307)) | ~m1_pre_topc(k1_tsep_1(A_305, B_306, C_307), A_305) | ~v1_pre_topc(k1_tsep_1(A_305, B_306, C_307)) | v2_struct_0(k1_tsep_1(A_305, B_306, C_307)) | ~m1_pre_topc(C_307, A_305) | v2_struct_0(C_307) | ~m1_pre_topc(B_306, A_305) | v2_struct_0(B_306) | ~l1_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_114])).
% 32.10/20.90  tff(c_2142, plain, (![A_348, B_349, C_350]: (u1_struct_0(k1_tsep_1(A_348, B_349, C_350))=k2_xboole_0(u1_struct_0(B_349), u1_struct_0(C_350)) | ~v1_pre_topc(k1_tsep_1(A_348, B_349, C_350)) | v2_struct_0(k1_tsep_1(A_348, B_349, C_350)) | ~m1_pre_topc(C_350, A_348) | v2_struct_0(C_350) | ~m1_pre_topc(B_349, A_348) | v2_struct_0(B_349) | ~l1_pre_topc(A_348) | v2_struct_0(A_348))), inference(resolution, [status(thm)], [c_58, c_1890])).
% 32.10/20.90  tff(c_62, plain, (![A_71, B_72, C_73]: (~v2_struct_0(k1_tsep_1(A_71, B_72, C_73)) | ~m1_pre_topc(C_73, A_71) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_71) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_145])).
% 32.10/20.90  tff(c_2454, plain, (![A_351, B_352, C_353]: (u1_struct_0(k1_tsep_1(A_351, B_352, C_353))=k2_xboole_0(u1_struct_0(B_352), u1_struct_0(C_353)) | ~v1_pre_topc(k1_tsep_1(A_351, B_352, C_353)) | ~m1_pre_topc(C_353, A_351) | v2_struct_0(C_353) | ~m1_pre_topc(B_352, A_351) | v2_struct_0(B_352) | ~l1_pre_topc(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_2142, c_62])).
% 32.10/20.90  tff(c_2458, plain, (![A_354, B_355, C_356]: (u1_struct_0(k1_tsep_1(A_354, B_355, C_356))=k2_xboole_0(u1_struct_0(B_355), u1_struct_0(C_356)) | ~m1_pre_topc(C_356, A_354) | v2_struct_0(C_356) | ~m1_pre_topc(B_355, A_354) | v2_struct_0(B_355) | ~l1_pre_topc(A_354) | v2_struct_0(A_354))), inference(resolution, [status(thm)], [c_60, c_2454])).
% 32.10/20.90  tff(c_2740, plain, (![A_354, C_356]: (u1_struct_0(k1_tsep_1(A_354, '#skF_6', C_356))=k2_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(C_356)) | ~m1_pre_topc(C_356, A_354) | v2_struct_0(C_356) | ~m1_pre_topc('#skF_6', A_354) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_354) | v2_struct_0(A_354))), inference(superposition, [status(thm), theory('equality')], [c_147, c_2458])).
% 32.10/20.90  tff(c_6296, plain, (![A_407, C_408]: (u1_struct_0(k1_tsep_1(A_407, '#skF_6', C_408))=k2_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(C_408)) | ~m1_pre_topc(C_408, A_407) | v2_struct_0(C_408) | ~m1_pre_topc('#skF_6', A_407) | ~l1_pre_topc(A_407) | v2_struct_0(A_407))), inference(negUnitSimplification, [status(thm)], [c_82, c_2740])).
% 32.10/20.90  tff(c_6652, plain, (![A_407]: (u1_struct_0(k1_tsep_1(A_407, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_407) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', A_407) | ~l1_pre_topc(A_407) | v2_struct_0(A_407))), inference(superposition, [status(thm), theory('equality')], [c_143, c_6296])).
% 32.10/20.90  tff(c_6700, plain, (![A_409]: (u1_struct_0(k1_tsep_1(A_409, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_409) | ~m1_pre_topc('#skF_6', A_409) | ~l1_pre_topc(A_409) | v2_struct_0(A_409))), inference(negUnitSimplification, [status(thm)], [c_86, c_6652])).
% 32.10/20.90  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.10/20.90  tff(c_164, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.10/20.90  tff(c_169, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(k2_xboole_0(A_6, B_7), A_6))), inference(resolution, [status(thm)], [c_14, c_164])).
% 32.10/20.90  tff(c_6967, plain, (![A_409]: (k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_6') | ~r1_tarski(u1_struct_0(k1_tsep_1(A_409, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_409) | ~m1_pre_topc('#skF_6', A_409) | ~l1_pre_topc(A_409) | v2_struct_0(A_409))), inference(superposition, [status(thm), theory('equality')], [c_6700, c_169])).
% 32.10/20.90  tff(c_23259, plain, (k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_6967])).
% 32.10/20.90  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 32.10/20.90  tff(c_23285, plain, (![A_817]: (r1_xboole_0(A_817, k2_struct_0('#skF_5')) | ~r1_xboole_0(A_817, k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_23259, c_10])).
% 32.10/20.90  tff(c_292, plain, (![B_121]: (r1_tsep_1('#skF_7', B_121) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_121)) | ~l1_struct_0(B_121) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_274])).
% 32.10/20.90  tff(c_649, plain, (![B_146]: (r1_tsep_1('#skF_7', B_146) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_146)) | ~l1_struct_0(B_146))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_292])).
% 32.10/20.90  tff(c_655, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_143, c_649])).
% 32.10/20.90  tff(c_667, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_655])).
% 32.10/20.90  tff(c_721, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_667])).
% 32.10/20.90  tff(c_23300, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_23285, c_721])).
% 32.10/20.90  tff(c_23308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_363, c_23300])).
% 32.10/20.90  tff(c_23350, plain, (![A_819]: (~r1_tarski(u1_struct_0(k1_tsep_1(A_819, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_819) | ~m1_pre_topc('#skF_6', A_819) | ~l1_pre_topc(A_819) | v2_struct_0(A_819))), inference(splitRight, [status(thm)], [c_6967])).
% 32.10/20.90  tff(c_23377, plain, (![A_212]: (~r1_tarski(k2_struct_0(k1_tsep_1(A_212, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_212) | ~m1_pre_topc('#skF_6', A_212) | ~l1_pre_topc(A_212) | v2_struct_0(A_212) | ~m1_pre_topc('#skF_5', A_212) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', A_212) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_212) | v2_struct_0(A_212))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_23350])).
% 32.10/20.90  tff(c_57754, plain, (![A_1359]: (~r1_tarski(k2_struct_0(k1_tsep_1(A_1359, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_1359) | ~m1_pre_topc('#skF_6', A_1359) | ~l1_pre_topc(A_1359) | v2_struct_0(A_1359) | ~m1_pre_topc('#skF_5', A_1359) | ~m1_pre_topc('#skF_6', A_1359) | ~l1_pre_topc(A_1359) | v2_struct_0(A_1359))), inference(negUnitSimplification, [status(thm)], [c_82, c_86, c_23377])).
% 32.10/20.90  tff(c_57764, plain, (![A_1359]: (~m1_pre_topc('#skF_5', A_1359) | ~m1_pre_topc('#skF_6', A_1359) | ~l1_pre_topc(A_1359) | v2_struct_0(A_1359) | ~m1_pre_topc(k1_tsep_1(A_1359, '#skF_6', '#skF_5'), '#skF_6') | ~l1_pre_topc(k1_tsep_1(A_1359, '#skF_6', '#skF_5')) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_57754])).
% 32.10/20.90  tff(c_57925, plain, (![A_1361]: (~m1_pre_topc('#skF_5', A_1361) | ~m1_pre_topc('#skF_6', A_1361) | ~l1_pre_topc(A_1361) | v2_struct_0(A_1361) | ~m1_pre_topc(k1_tsep_1(A_1361, '#skF_6', '#skF_5'), '#skF_6') | ~l1_pre_topc(k1_tsep_1(A_1361, '#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_57764])).
% 32.10/20.90  tff(c_57929, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_58, c_57925])).
% 32.10/20.90  tff(c_57932, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_6', '#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_438, c_74, c_57929])).
% 32.10/20.90  tff(c_57933, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_86, c_57932])).
% 32.10/20.90  tff(c_57936, plain, (~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_760, c_57933])).
% 32.10/20.90  tff(c_57939, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_438, c_74, c_57936])).
% 32.10/20.90  tff(c_57941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_86, c_57939])).
% 32.10/20.90  tff(c_57942, plain, (r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_667])).
% 32.10/20.90  tff(c_64, plain, (![B_75, A_74]: (r1_tsep_1(B_75, A_74) | ~r1_tsep_1(A_74, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_153])).
% 32.10/20.90  tff(c_57945, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_57942, c_64])).
% 32.10/20.90  tff(c_57948, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_587, c_57945])).
% 32.10/20.90  tff(c_57950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_57948])).
% 32.10/20.90  tff(c_57952, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 32.10/20.90  tff(c_57951, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 32.10/20.90  tff(c_58040, plain, (![B_1373, A_1374]: (r1_tsep_1(B_1373, A_1374) | ~r1_tsep_1(A_1374, B_1373) | ~l1_struct_0(B_1373) | ~l1_struct_0(A_1374))), inference(cnfTransformation, [status(thm)], [f_153])).
% 32.10/20.90  tff(c_58042, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_57951, c_58040])).
% 32.10/20.90  tff(c_58045, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_57952, c_58042])).
% 32.10/20.90  tff(c_58046, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_58045])).
% 32.10/20.90  tff(c_58049, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_58046])).
% 32.10/20.90  tff(c_58053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57977, c_58049])).
% 32.10/20.90  tff(c_58054, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_58045])).
% 32.10/20.90  tff(c_58063, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_46, c_58054])).
% 32.10/20.90  tff(c_58067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58001, c_58063])).
% 32.10/20.90  tff(c_58068, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 32.10/20.90  tff(c_58069, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 32.10/20.90  tff(c_58142, plain, (![B_1388, A_1389]: (r1_tsep_1(B_1388, A_1389) | ~r1_tsep_1(A_1389, B_1388) | ~l1_struct_0(B_1388) | ~l1_struct_0(A_1389))), inference(cnfTransformation, [status(thm)], [f_153])).
% 32.10/20.90  tff(c_58146, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58069, c_58142])).
% 32.10/20.90  tff(c_58150, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58068, c_58146])).
% 32.10/20.90  tff(c_58151, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_58150])).
% 32.10/20.90  tff(c_58154, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_58151])).
% 32.10/20.90  tff(c_58158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58094, c_58154])).
% 32.10/20.90  tff(c_58159, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_58150])).
% 32.10/20.90  tff(c_58163, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_58159])).
% 32.10/20.90  tff(c_58167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58091, c_58163])).
% 32.10/20.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.10/20.90  
% 32.10/20.90  Inference rules
% 32.10/20.90  ----------------------
% 32.10/20.90  #Ref     : 2
% 32.10/20.90  #Sup     : 16345
% 32.10/20.90  #Fact    : 2
% 32.10/20.90  #Define  : 0
% 32.10/20.90  #Split   : 85
% 32.10/20.90  #Chain   : 0
% 32.10/20.90  #Close   : 0
% 32.10/20.90  
% 32.10/20.90  Ordering : KBO
% 32.10/20.90  
% 32.10/20.90  Simplification rules
% 32.10/20.90  ----------------------
% 32.10/20.90  #Subsume      : 4140
% 32.10/20.90  #Demod        : 5119
% 32.10/20.90  #Tautology    : 1272
% 32.10/20.90  #SimpNegUnit  : 3829
% 32.10/20.90  #BackRed      : 259
% 32.10/20.90  
% 32.10/20.90  #Partial instantiations: 0
% 32.10/20.90  #Strategies tried      : 1
% 32.10/20.90  
% 32.10/20.90  Timing (in seconds)
% 32.10/20.90  ----------------------
% 32.10/20.90  Preprocessing        : 0.38
% 32.10/20.90  Parsing              : 0.19
% 32.10/20.90  CNF conversion       : 0.03
% 32.10/20.90  Main loop            : 19.74
% 32.10/20.90  Inferencing          : 3.11
% 32.10/20.90  Reduction            : 5.26
% 32.10/20.90  Demodulation         : 3.67
% 32.10/20.90  BG Simplification    : 0.42
% 32.10/20.90  Subsumption          : 9.91
% 32.10/20.90  Abstraction          : 0.57
% 32.10/20.90  MUC search           : 0.00
% 32.10/20.90  Cooper               : 0.00
% 32.10/20.90  Total                : 20.17
% 32.10/20.90  Index Insertion      : 0.00
% 32.10/20.90  Index Deletion       : 0.00
% 32.10/20.90  Index Matching       : 0.00
% 32.10/20.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
