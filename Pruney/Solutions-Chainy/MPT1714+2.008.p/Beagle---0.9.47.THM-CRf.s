%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 45.08s
% Output     : CNFRefutation 45.26s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 831 expanded)
%              Number of leaves         :   41 ( 280 expanded)
%              Depth                    :   20
%              Number of atoms          :  455 (3276 expanded)
%              Number of equality atoms :   23 ( 126 expanded)
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

tff(f_207,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_125,axiom,(
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

tff(f_169,axiom,(
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

tff(f_147,axiom,(
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

tff(f_76,axiom,(
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

tff(f_116,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86317,plain,(
    ! [B_1982,A_1983] :
      ( l1_pre_topc(B_1982)
      | ~ m1_pre_topc(B_1982,A_1983)
      | ~ l1_pre_topc(A_1983) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_86320,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_86317])).

tff(c_86332,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86320])).

tff(c_46,plain,(
    ! [A_50] :
      ( l1_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_84,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86323,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_86317])).

tff(c_86335,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86323])).

tff(c_80,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86181,plain,(
    ! [B_1959,A_1960] :
      ( l1_pre_topc(B_1959)
      | ~ m1_pre_topc(B_1959,A_1960)
      | ~ l1_pre_topc(A_1960) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_86193,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_86181])).

tff(c_86203,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86193])).

tff(c_74,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86200,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_86181])).

tff(c_86204,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86200])).

tff(c_86218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86203,c_86204])).

tff(c_86220,plain,(
    l1_pre_topc('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86200])).

tff(c_86184,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_86181])).

tff(c_86196,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86184])).

tff(c_72,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_96,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_112,plain,(
    ! [B_99,A_100] :
      ( l1_pre_topc(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_112])).

tff(c_127,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_115])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_112])).

tff(c_134,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_124])).

tff(c_70,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_97,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_204,plain,(
    ! [B_123,A_124] :
      ( r1_tsep_1(B_123,A_124)
      | ~ r1_tsep_1(A_124,B_123)
      | ~ l1_struct_0(B_123)
      | ~ l1_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_207,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_97,c_204])).

tff(c_208,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_211,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_211])).

tff(c_216,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_223,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_226,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_226])).

tff(c_232,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_118,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_112])).

tff(c_130,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_118])).

tff(c_98,plain,(
    ! [A_97] :
      ( u1_struct_0(A_97) = k2_struct_0(A_97)
      | ~ l1_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_146,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_130,c_102])).

tff(c_138,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_127,c_102])).

tff(c_261,plain,(
    ! [A_133,B_134] :
      ( r1_tsep_1(A_133,B_134)
      | ~ r1_xboole_0(u1_struct_0(A_133),u1_struct_0(B_134))
      | ~ l1_struct_0(B_134)
      | ~ l1_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_279,plain,(
    ! [A_133] :
      ( r1_tsep_1(A_133,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_133),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_261])).

tff(c_389,plain,(
    ! [A_139] :
      ( r1_tsep_1(A_139,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_139),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_279])).

tff(c_392,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_389])).

tff(c_402,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_392])).

tff(c_409,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_412,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_409])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_412])).

tff(c_418,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_90,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_529,plain,(
    ! [B_148,C_149,A_150] :
      ( m1_pre_topc(B_148,C_149)
      | ~ r1_tarski(u1_struct_0(B_148),u1_struct_0(C_149))
      | ~ m1_pre_topc(C_149,A_150)
      | ~ m1_pre_topc(B_148,A_150)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_550,plain,(
    ! [B_151,A_152] :
      ( m1_pre_topc(B_151,B_151)
      | ~ m1_pre_topc(B_151,A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_6,c_529])).

tff(c_558,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_550])).

tff(c_570,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_558])).

tff(c_784,plain,(
    ! [A_166,B_167,C_168] :
      ( m1_pre_topc(k1_tsep_1(A_166,B_167,C_168),A_166)
      | ~ m1_pre_topc(C_168,A_166)
      | v2_struct_0(C_168)
      | ~ m1_pre_topc(B_167,A_166)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48,plain,(
    ! [B_53,A_51] :
      ( l1_pre_topc(B_53)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_794,plain,(
    ! [A_166,B_167,C_168] :
      ( l1_pre_topc(k1_tsep_1(A_166,B_167,C_168))
      | ~ m1_pre_topc(C_168,A_166)
      | v2_struct_0(C_168)
      | ~ m1_pre_topc(B_167,A_166)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_784,c_48])).

tff(c_58,plain,(
    ! [A_72,B_73,C_74] :
      ( m1_pre_topc(k1_tsep_1(A_72,B_73,C_74),A_72)
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    ! [B_32,A_10] :
      ( r1_tarski(k2_struct_0(B_32),k2_struct_0(A_10))
      | ~ m1_pre_topc(B_32,A_10)
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1452,plain,(
    ! [A_253,B_254,C_255] :
      ( l1_pre_topc(k1_tsep_1(A_253,B_254,C_255))
      | ~ m1_pre_topc(C_255,A_253)
      | v2_struct_0(C_255)
      | ~ m1_pre_topc(B_254,A_253)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_784,c_48])).

tff(c_1456,plain,(
    ! [A_253,B_254,C_255] :
      ( u1_struct_0(k1_tsep_1(A_253,B_254,C_255)) = k2_struct_0(k1_tsep_1(A_253,B_254,C_255))
      | ~ m1_pre_topc(C_255,A_253)
      | v2_struct_0(C_255)
      | ~ m1_pre_topc(B_254,A_253)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_1452,c_102])).

tff(c_217,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_231,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_142,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_134,c_102])).

tff(c_347,plain,(
    ! [A_137,B_138] :
      ( r1_xboole_0(u1_struct_0(A_137),u1_struct_0(B_138))
      | ~ r1_tsep_1(A_137,B_138)
      | ~ l1_struct_0(B_138)
      | ~ l1_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_365,plain,(
    ! [B_138] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_138))
      | ~ r1_tsep_1('#skF_7',B_138)
      | ~ l1_struct_0(B_138)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_347])).

tff(c_621,plain,(
    ! [B_153] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_153))
      | ~ r1_tsep_1('#skF_7',B_153)
      | ~ l1_struct_0(B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_365])).

tff(c_627,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_621])).

tff(c_637,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_231,c_627])).

tff(c_60,plain,(
    ! [A_72,B_73,C_74] :
      ( v1_pre_topc(k1_tsep_1(A_72,B_73,C_74))
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1955,plain,(
    ! [A_425,B_426,C_427] :
      ( u1_struct_0(k1_tsep_1(A_425,B_426,C_427)) = k2_xboole_0(u1_struct_0(B_426),u1_struct_0(C_427))
      | ~ m1_pre_topc(k1_tsep_1(A_425,B_426,C_427),A_425)
      | ~ v1_pre_topc(k1_tsep_1(A_425,B_426,C_427))
      | v2_struct_0(k1_tsep_1(A_425,B_426,C_427))
      | ~ m1_pre_topc(C_427,A_425)
      | v2_struct_0(C_427)
      | ~ m1_pre_topc(B_426,A_425)
      | v2_struct_0(B_426)
      | ~ l1_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2179,plain,(
    ! [A_482,B_483,C_484] :
      ( u1_struct_0(k1_tsep_1(A_482,B_483,C_484)) = k2_xboole_0(u1_struct_0(B_483),u1_struct_0(C_484))
      | ~ v1_pre_topc(k1_tsep_1(A_482,B_483,C_484))
      | v2_struct_0(k1_tsep_1(A_482,B_483,C_484))
      | ~ m1_pre_topc(C_484,A_482)
      | v2_struct_0(C_484)
      | ~ m1_pre_topc(B_483,A_482)
      | v2_struct_0(B_483)
      | ~ l1_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_58,c_1955])).

tff(c_62,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ v2_struct_0(k1_tsep_1(A_72,B_73,C_74))
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2537,plain,(
    ! [A_485,B_486,C_487] :
      ( u1_struct_0(k1_tsep_1(A_485,B_486,C_487)) = k2_xboole_0(u1_struct_0(B_486),u1_struct_0(C_487))
      | ~ v1_pre_topc(k1_tsep_1(A_485,B_486,C_487))
      | ~ m1_pre_topc(C_487,A_485)
      | v2_struct_0(C_487)
      | ~ m1_pre_topc(B_486,A_485)
      | v2_struct_0(B_486)
      | ~ l1_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(resolution,[status(thm)],[c_2179,c_62])).

tff(c_2541,plain,(
    ! [A_488,B_489,C_490] :
      ( u1_struct_0(k1_tsep_1(A_488,B_489,C_490)) = k2_xboole_0(u1_struct_0(B_489),u1_struct_0(C_490))
      | ~ m1_pre_topc(C_490,A_488)
      | v2_struct_0(C_490)
      | ~ m1_pre_topc(B_489,A_488)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(resolution,[status(thm)],[c_60,c_2537])).

tff(c_2866,plain,(
    ! [A_488,B_489] :
      ( u1_struct_0(k1_tsep_1(A_488,B_489,'#skF_5')) = k2_xboole_0(u1_struct_0(B_489),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_488)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_489,A_488)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_2541])).

tff(c_7705,plain,(
    ! [A_564,B_565] :
      ( u1_struct_0(k1_tsep_1(A_564,B_565,'#skF_5')) = k2_xboole_0(u1_struct_0(B_565),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_564)
      | ~ m1_pre_topc(B_565,A_564)
      | v2_struct_0(B_565)
      | ~ l1_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2866])).

tff(c_8138,plain,(
    ! [A_564] :
      ( u1_struct_0(k1_tsep_1(A_564,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_564)
      | ~ m1_pre_topc('#skF_6',A_564)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_7705])).

tff(c_9500,plain,(
    ! [A_579] :
      ( u1_struct_0(k1_tsep_1(A_579,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_579)
      | ~ m1_pre_topc('#skF_6',A_579)
      | ~ l1_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_8138])).

tff(c_170,plain,(
    ! [A_109,C_110,B_111] :
      ( r1_tarski(A_109,C_110)
      | ~ r1_tarski(k2_xboole_0(A_109,B_111),C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_112,B_113] : r1_tarski(A_112,k2_xboole_0(A_112,B_113)) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [A_112,B_113] :
      ( k2_xboole_0(A_112,B_113) = A_112
      | ~ r1_tarski(k2_xboole_0(A_112,B_113),A_112) ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_9823,plain,(
    ! [A_579] :
      ( k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_6')
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(A_579,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_579)
      | ~ m1_pre_topc('#skF_6',A_579)
      | ~ l1_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9500,c_184])).

tff(c_60776,plain,(
    k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9823])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60877,plain,(
    ! [A_1541] :
      ( r1_xboole_0(A_1541,k2_struct_0('#skF_5'))
      | ~ r1_xboole_0(A_1541,k2_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60776,c_12])).

tff(c_624,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_621])).

tff(c_635,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_624])).

tff(c_645,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_276,plain,(
    ! [B_134] :
      ( r1_tsep_1('#skF_7',B_134)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_134))
      | ~ l1_struct_0(B_134)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_261])).

tff(c_727,plain,(
    ! [B_164] :
      ( r1_tsep_1('#skF_7',B_164)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_164))
      | ~ l1_struct_0(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_276])).

tff(c_733,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_727])).

tff(c_745,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_733])).

tff(c_746,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_745])).

tff(c_60901,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_60877,c_746])).

tff(c_60912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_60901])).

tff(c_61032,plain,(
    ! [A_1546] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(A_1546,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_1546)
      | ~ m1_pre_topc('#skF_6',A_1546)
      | ~ l1_pre_topc(A_1546)
      | v2_struct_0(A_1546) ) ),
    inference(splitRight,[status(thm)],[c_9823])).

tff(c_61059,plain,(
    ! [A_253] :
      ( ~ r1_tarski(k2_struct_0(k1_tsep_1(A_253,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_253)
      | ~ m1_pre_topc('#skF_6',A_253)
      | ~ l1_pre_topc(A_253)
      | v2_struct_0(A_253)
      | ~ m1_pre_topc('#skF_5',A_253)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_6',A_253)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_61032])).

tff(c_86123,plain,(
    ! [A_1955] :
      ( ~ r1_tarski(k2_struct_0(k1_tsep_1(A_1955,'#skF_6','#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_5',A_1955)
      | ~ m1_pre_topc('#skF_6',A_1955)
      | ~ l1_pre_topc(A_1955)
      | v2_struct_0(A_1955)
      | ~ m1_pre_topc('#skF_5',A_1955)
      | ~ m1_pre_topc('#skF_6',A_1955)
      | ~ l1_pre_topc(A_1955)
      | v2_struct_0(A_1955) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86,c_61059])).

tff(c_86133,plain,(
    ! [A_1955] :
      ( ~ m1_pre_topc('#skF_5',A_1955)
      | ~ m1_pre_topc('#skF_6',A_1955)
      | ~ l1_pre_topc(A_1955)
      | v2_struct_0(A_1955)
      | ~ m1_pre_topc(k1_tsep_1(A_1955,'#skF_6','#skF_5'),'#skF_6')
      | ~ l1_pre_topc(k1_tsep_1(A_1955,'#skF_6','#skF_5'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_86123])).

tff(c_86139,plain,(
    ! [A_1956] :
      ( ~ m1_pre_topc('#skF_5',A_1956)
      | ~ m1_pre_topc('#skF_6',A_1956)
      | ~ l1_pre_topc(A_1956)
      | v2_struct_0(A_1956)
      | ~ m1_pre_topc(k1_tsep_1(A_1956,'#skF_6','#skF_5'),'#skF_6')
      | ~ l1_pre_topc(k1_tsep_1(A_1956,'#skF_6','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_86133])).

tff(c_86143,plain,
    ( ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_86139])).

tff(c_86146,plain,
    ( ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_6','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_570,c_74,c_86143])).

tff(c_86147,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86,c_86146])).

tff(c_86150,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_794,c_86147])).

tff(c_86153,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_570,c_74,c_86150])).

tff(c_86155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86,c_86153])).

tff(c_86157,plain,(
    r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_64,plain,(
    ! [B_76,A_75] :
      ( r1_tsep_1(B_76,A_75)
      | ~ r1_tsep_1(A_75,B_76)
      | ~ l1_struct_0(B_76)
      | ~ l1_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_86159,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86157,c_64])).

tff(c_86162,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_418,c_86159])).

tff(c_86164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_86162])).

tff(c_86166,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_86165,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_86281,plain,(
    ! [B_1979,A_1980] :
      ( r1_tsep_1(B_1979,A_1980)
      | ~ r1_tsep_1(A_1980,B_1979)
      | ~ l1_struct_0(B_1979)
      | ~ l1_struct_0(A_1980) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_86283,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86165,c_86281])).

tff(c_86286,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_86166,c_86283])).

tff(c_86287,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_86286])).

tff(c_86290,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_86287])).

tff(c_86294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86196,c_86290])).

tff(c_86295,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86286])).

tff(c_86304,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_86295])).

tff(c_86308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86220,c_86304])).

tff(c_86309,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_86310,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_86408,plain,(
    ! [B_2001,A_2002] :
      ( r1_tsep_1(B_2001,A_2002)
      | ~ r1_tsep_1(A_2002,B_2001)
      | ~ l1_struct_0(B_2001)
      | ~ l1_struct_0(A_2002) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_86412,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_86310,c_86408])).

tff(c_86416,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86309,c_86412])).

tff(c_86417,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86416])).

tff(c_86420,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_86417])).

tff(c_86424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86335,c_86420])).

tff(c_86425,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_86416])).

tff(c_86429,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_86425])).

tff(c_86433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86332,c_86429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.08/32.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.12/32.21  
% 45.12/32.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.12/32.22  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 45.12/32.22  
% 45.12/32.22  %Foreground sorts:
% 45.12/32.22  
% 45.12/32.22  
% 45.12/32.22  %Background operators:
% 45.12/32.22  
% 45.12/32.22  
% 45.12/32.22  %Foreground operators:
% 45.12/32.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 45.12/32.22  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 45.12/32.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 45.12/32.22  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 45.12/32.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.12/32.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 45.12/32.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 45.12/32.22  tff('#skF_7', type, '#skF_7': $i).
% 45.12/32.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 45.12/32.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.12/32.22  tff('#skF_5', type, '#skF_5': $i).
% 45.12/32.22  tff('#skF_6', type, '#skF_6': $i).
% 45.12/32.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 45.12/32.22  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 45.12/32.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 45.12/32.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 45.12/32.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.12/32.22  tff('#skF_4', type, '#skF_4': $i).
% 45.12/32.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.12/32.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 45.12/32.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 45.12/32.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 45.12/32.22  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 45.12/32.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 45.12/32.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 45.12/32.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 45.12/32.22  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 45.12/32.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 45.12/32.22  
% 45.26/32.24  tff(f_207, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 45.26/32.24  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 45.26/32.24  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 45.26/32.24  tff(f_155, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 45.26/32.24  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 45.26/32.24  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 45.26/32.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 45.26/32.24  tff(f_169, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 45.26/32.24  tff(f_147, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 45.26/32.24  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 45.26/32.24  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 45.26/32.24  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 45.26/32.24  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 45.26/32.24  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_76, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_86317, plain, (![B_1982, A_1983]: (l1_pre_topc(B_1982) | ~m1_pre_topc(B_1982, A_1983) | ~l1_pre_topc(A_1983))), inference(cnfTransformation, [status(thm)], [f_87])).
% 45.26/32.24  tff(c_86320, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_86317])).
% 45.26/32.24  tff(c_86332, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86320])).
% 45.26/32.24  tff(c_46, plain, (![A_50]: (l1_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 45.26/32.24  tff(c_84, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_86323, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_84, c_86317])).
% 45.26/32.24  tff(c_86335, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86323])).
% 45.26/32.24  tff(c_80, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_86181, plain, (![B_1959, A_1960]: (l1_pre_topc(B_1959) | ~m1_pre_topc(B_1959, A_1960) | ~l1_pre_topc(A_1960))), inference(cnfTransformation, [status(thm)], [f_87])).
% 45.26/32.24  tff(c_86193, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_80, c_86181])).
% 45.26/32.24  tff(c_86203, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86193])).
% 45.26/32.24  tff(c_74, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_86200, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_74, c_86181])).
% 45.26/32.24  tff(c_86204, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_86200])).
% 45.26/32.24  tff(c_86218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86203, c_86204])).
% 45.26/32.24  tff(c_86220, plain, (l1_pre_topc('#skF_6')), inference(splitRight, [status(thm)], [c_86200])).
% 45.26/32.24  tff(c_86184, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_86181])).
% 45.26/32.24  tff(c_86196, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86184])).
% 45.26/32.24  tff(c_72, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_96, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_72])).
% 45.26/32.24  tff(c_112, plain, (![B_99, A_100]: (l1_pre_topc(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_87])).
% 45.26/32.24  tff(c_115, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_112])).
% 45.26/32.24  tff(c_127, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_115])).
% 45.26/32.24  tff(c_124, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_80, c_112])).
% 45.26/32.24  tff(c_134, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_124])).
% 45.26/32.24  tff(c_70, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_97, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 45.26/32.24  tff(c_204, plain, (![B_123, A_124]: (r1_tsep_1(B_123, A_124) | ~r1_tsep_1(A_124, B_123) | ~l1_struct_0(B_123) | ~l1_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_155])).
% 45.26/32.24  tff(c_207, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_97, c_204])).
% 45.26/32.24  tff(c_208, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_207])).
% 45.26/32.24  tff(c_211, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_46, c_208])).
% 45.26/32.24  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_211])).
% 45.26/32.24  tff(c_216, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_207])).
% 45.26/32.24  tff(c_223, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_216])).
% 45.26/32.24  tff(c_226, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_223])).
% 45.26/32.24  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_226])).
% 45.26/32.24  tff(c_232, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_216])).
% 45.26/32.24  tff(c_118, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_84, c_112])).
% 45.26/32.24  tff(c_130, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_118])).
% 45.26/32.24  tff(c_98, plain, (![A_97]: (u1_struct_0(A_97)=k2_struct_0(A_97) | ~l1_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_55])).
% 45.26/32.24  tff(c_102, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_46, c_98])).
% 45.26/32.24  tff(c_146, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_130, c_102])).
% 45.26/32.24  tff(c_138, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_127, c_102])).
% 45.26/32.24  tff(c_261, plain, (![A_133, B_134]: (r1_tsep_1(A_133, B_134) | ~r1_xboole_0(u1_struct_0(A_133), u1_struct_0(B_134)) | ~l1_struct_0(B_134) | ~l1_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_125])).
% 45.26/32.24  tff(c_279, plain, (![A_133]: (r1_tsep_1(A_133, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_133), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_133))), inference(superposition, [status(thm), theory('equality')], [c_138, c_261])).
% 45.26/32.24  tff(c_389, plain, (![A_139]: (r1_tsep_1(A_139, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_139), k2_struct_0('#skF_7')) | ~l1_struct_0(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_279])).
% 45.26/32.24  tff(c_392, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_146, c_389])).
% 45.26/32.24  tff(c_402, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_96, c_392])).
% 45.26/32.24  tff(c_409, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_402])).
% 45.26/32.24  tff(c_412, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_409])).
% 45.26/32.24  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_412])).
% 45.26/32.24  tff(c_418, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_402])).
% 45.26/32.24  tff(c_82, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_86, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_90, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 45.26/32.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.26/32.24  tff(c_529, plain, (![B_148, C_149, A_150]: (m1_pre_topc(B_148, C_149) | ~r1_tarski(u1_struct_0(B_148), u1_struct_0(C_149)) | ~m1_pre_topc(C_149, A_150) | ~m1_pre_topc(B_148, A_150) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_169])).
% 45.26/32.24  tff(c_550, plain, (![B_151, A_152]: (m1_pre_topc(B_151, B_151) | ~m1_pre_topc(B_151, A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(resolution, [status(thm)], [c_6, c_529])).
% 45.26/32.24  tff(c_558, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_80, c_550])).
% 45.26/32.24  tff(c_570, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_558])).
% 45.26/32.24  tff(c_784, plain, (![A_166, B_167, C_168]: (m1_pre_topc(k1_tsep_1(A_166, B_167, C_168), A_166) | ~m1_pre_topc(C_168, A_166) | v2_struct_0(C_168) | ~m1_pre_topc(B_167, A_166) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_147])).
% 45.26/32.24  tff(c_48, plain, (![B_53, A_51]: (l1_pre_topc(B_53) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 45.26/32.24  tff(c_794, plain, (![A_166, B_167, C_168]: (l1_pre_topc(k1_tsep_1(A_166, B_167, C_168)) | ~m1_pre_topc(C_168, A_166) | v2_struct_0(C_168) | ~m1_pre_topc(B_167, A_166) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_784, c_48])).
% 45.26/32.24  tff(c_58, plain, (![A_72, B_73, C_74]: (m1_pre_topc(k1_tsep_1(A_72, B_73, C_74), A_72) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_147])).
% 45.26/32.24  tff(c_36, plain, (![B_32, A_10]: (r1_tarski(k2_struct_0(B_32), k2_struct_0(A_10)) | ~m1_pre_topc(B_32, A_10) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.26/32.24  tff(c_1452, plain, (![A_253, B_254, C_255]: (l1_pre_topc(k1_tsep_1(A_253, B_254, C_255)) | ~m1_pre_topc(C_255, A_253) | v2_struct_0(C_255) | ~m1_pre_topc(B_254, A_253) | v2_struct_0(B_254) | ~l1_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_784, c_48])).
% 45.26/32.24  tff(c_1456, plain, (![A_253, B_254, C_255]: (u1_struct_0(k1_tsep_1(A_253, B_254, C_255))=k2_struct_0(k1_tsep_1(A_253, B_254, C_255)) | ~m1_pre_topc(C_255, A_253) | v2_struct_0(C_255) | ~m1_pre_topc(B_254, A_253) | v2_struct_0(B_254) | ~l1_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_1452, c_102])).
% 45.26/32.24  tff(c_217, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_207])).
% 45.26/32.24  tff(c_231, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_216])).
% 45.26/32.24  tff(c_142, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_134, c_102])).
% 45.26/32.24  tff(c_347, plain, (![A_137, B_138]: (r1_xboole_0(u1_struct_0(A_137), u1_struct_0(B_138)) | ~r1_tsep_1(A_137, B_138) | ~l1_struct_0(B_138) | ~l1_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_125])).
% 45.26/32.24  tff(c_365, plain, (![B_138]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_138)) | ~r1_tsep_1('#skF_7', B_138) | ~l1_struct_0(B_138) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_347])).
% 45.26/32.24  tff(c_621, plain, (![B_153]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_153)) | ~r1_tsep_1('#skF_7', B_153) | ~l1_struct_0(B_153))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_365])).
% 45.26/32.24  tff(c_627, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_142, c_621])).
% 45.26/32.24  tff(c_637, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_231, c_627])).
% 45.26/32.24  tff(c_60, plain, (![A_72, B_73, C_74]: (v1_pre_topc(k1_tsep_1(A_72, B_73, C_74)) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_147])).
% 45.26/32.24  tff(c_1955, plain, (![A_425, B_426, C_427]: (u1_struct_0(k1_tsep_1(A_425, B_426, C_427))=k2_xboole_0(u1_struct_0(B_426), u1_struct_0(C_427)) | ~m1_pre_topc(k1_tsep_1(A_425, B_426, C_427), A_425) | ~v1_pre_topc(k1_tsep_1(A_425, B_426, C_427)) | v2_struct_0(k1_tsep_1(A_425, B_426, C_427)) | ~m1_pre_topc(C_427, A_425) | v2_struct_0(C_427) | ~m1_pre_topc(B_426, A_425) | v2_struct_0(B_426) | ~l1_pre_topc(A_425) | v2_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_116])).
% 45.26/32.24  tff(c_2179, plain, (![A_482, B_483, C_484]: (u1_struct_0(k1_tsep_1(A_482, B_483, C_484))=k2_xboole_0(u1_struct_0(B_483), u1_struct_0(C_484)) | ~v1_pre_topc(k1_tsep_1(A_482, B_483, C_484)) | v2_struct_0(k1_tsep_1(A_482, B_483, C_484)) | ~m1_pre_topc(C_484, A_482) | v2_struct_0(C_484) | ~m1_pre_topc(B_483, A_482) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_58, c_1955])).
% 45.26/32.24  tff(c_62, plain, (![A_72, B_73, C_74]: (~v2_struct_0(k1_tsep_1(A_72, B_73, C_74)) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_147])).
% 45.26/32.24  tff(c_2537, plain, (![A_485, B_486, C_487]: (u1_struct_0(k1_tsep_1(A_485, B_486, C_487))=k2_xboole_0(u1_struct_0(B_486), u1_struct_0(C_487)) | ~v1_pre_topc(k1_tsep_1(A_485, B_486, C_487)) | ~m1_pre_topc(C_487, A_485) | v2_struct_0(C_487) | ~m1_pre_topc(B_486, A_485) | v2_struct_0(B_486) | ~l1_pre_topc(A_485) | v2_struct_0(A_485))), inference(resolution, [status(thm)], [c_2179, c_62])).
% 45.26/32.24  tff(c_2541, plain, (![A_488, B_489, C_490]: (u1_struct_0(k1_tsep_1(A_488, B_489, C_490))=k2_xboole_0(u1_struct_0(B_489), u1_struct_0(C_490)) | ~m1_pre_topc(C_490, A_488) | v2_struct_0(C_490) | ~m1_pre_topc(B_489, A_488) | v2_struct_0(B_489) | ~l1_pre_topc(A_488) | v2_struct_0(A_488))), inference(resolution, [status(thm)], [c_60, c_2537])).
% 45.26/32.24  tff(c_2866, plain, (![A_488, B_489]: (u1_struct_0(k1_tsep_1(A_488, B_489, '#skF_5'))=k2_xboole_0(u1_struct_0(B_489), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_488) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_489, A_488) | v2_struct_0(B_489) | ~l1_pre_topc(A_488) | v2_struct_0(A_488))), inference(superposition, [status(thm), theory('equality')], [c_146, c_2541])).
% 45.26/32.24  tff(c_7705, plain, (![A_564, B_565]: (u1_struct_0(k1_tsep_1(A_564, B_565, '#skF_5'))=k2_xboole_0(u1_struct_0(B_565), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_564) | ~m1_pre_topc(B_565, A_564) | v2_struct_0(B_565) | ~l1_pre_topc(A_564) | v2_struct_0(A_564))), inference(negUnitSimplification, [status(thm)], [c_86, c_2866])).
% 45.26/32.24  tff(c_8138, plain, (![A_564]: (u1_struct_0(k1_tsep_1(A_564, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_564) | ~m1_pre_topc('#skF_6', A_564) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_564) | v2_struct_0(A_564))), inference(superposition, [status(thm), theory('equality')], [c_142, c_7705])).
% 45.26/32.24  tff(c_9500, plain, (![A_579]: (u1_struct_0(k1_tsep_1(A_579, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_579) | ~m1_pre_topc('#skF_6', A_579) | ~l1_pre_topc(A_579) | v2_struct_0(A_579))), inference(negUnitSimplification, [status(thm)], [c_82, c_8138])).
% 45.26/32.24  tff(c_170, plain, (![A_109, C_110, B_111]: (r1_tarski(A_109, C_110) | ~r1_tarski(k2_xboole_0(A_109, B_111), C_110))), inference(cnfTransformation, [status(thm)], [f_35])).
% 45.26/32.24  tff(c_176, plain, (![A_112, B_113]: (r1_tarski(A_112, k2_xboole_0(A_112, B_113)))), inference(resolution, [status(thm)], [c_6, c_170])).
% 45.26/32.24  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.26/32.24  tff(c_184, plain, (![A_112, B_113]: (k2_xboole_0(A_112, B_113)=A_112 | ~r1_tarski(k2_xboole_0(A_112, B_113), A_112))), inference(resolution, [status(thm)], [c_176, c_2])).
% 45.26/32.24  tff(c_9823, plain, (![A_579]: (k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_6') | ~r1_tarski(u1_struct_0(k1_tsep_1(A_579, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_579) | ~m1_pre_topc('#skF_6', A_579) | ~l1_pre_topc(A_579) | v2_struct_0(A_579))), inference(superposition, [status(thm), theory('equality')], [c_9500, c_184])).
% 45.26/32.24  tff(c_60776, plain, (k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9823])).
% 45.26/32.24  tff(c_12, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 45.26/32.24  tff(c_60877, plain, (![A_1541]: (r1_xboole_0(A_1541, k2_struct_0('#skF_5')) | ~r1_xboole_0(A_1541, k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_60776, c_12])).
% 45.26/32.24  tff(c_624, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_146, c_621])).
% 45.26/32.24  tff(c_635, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_624])).
% 45.26/32.24  tff(c_645, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_635])).
% 45.26/32.24  tff(c_276, plain, (![B_134]: (r1_tsep_1('#skF_7', B_134) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_134)) | ~l1_struct_0(B_134) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_261])).
% 45.26/32.24  tff(c_727, plain, (![B_164]: (r1_tsep_1('#skF_7', B_164) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_164)) | ~l1_struct_0(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_276])).
% 45.26/32.24  tff(c_733, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_146, c_727])).
% 45.26/32.24  tff(c_745, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_733])).
% 45.26/32.24  tff(c_746, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_645, c_745])).
% 45.26/32.24  tff(c_60901, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_60877, c_746])).
% 45.26/32.24  tff(c_60912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_637, c_60901])).
% 45.26/32.24  tff(c_61032, plain, (![A_1546]: (~r1_tarski(u1_struct_0(k1_tsep_1(A_1546, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_1546) | ~m1_pre_topc('#skF_6', A_1546) | ~l1_pre_topc(A_1546) | v2_struct_0(A_1546))), inference(splitRight, [status(thm)], [c_9823])).
% 45.26/32.24  tff(c_61059, plain, (![A_253]: (~r1_tarski(k2_struct_0(k1_tsep_1(A_253, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_253) | ~m1_pre_topc('#skF_6', A_253) | ~l1_pre_topc(A_253) | v2_struct_0(A_253) | ~m1_pre_topc('#skF_5', A_253) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', A_253) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_253) | v2_struct_0(A_253))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_61032])).
% 45.26/32.24  tff(c_86123, plain, (![A_1955]: (~r1_tarski(k2_struct_0(k1_tsep_1(A_1955, '#skF_6', '#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', A_1955) | ~m1_pre_topc('#skF_6', A_1955) | ~l1_pre_topc(A_1955) | v2_struct_0(A_1955) | ~m1_pre_topc('#skF_5', A_1955) | ~m1_pre_topc('#skF_6', A_1955) | ~l1_pre_topc(A_1955) | v2_struct_0(A_1955))), inference(negUnitSimplification, [status(thm)], [c_82, c_86, c_61059])).
% 45.26/32.24  tff(c_86133, plain, (![A_1955]: (~m1_pre_topc('#skF_5', A_1955) | ~m1_pre_topc('#skF_6', A_1955) | ~l1_pre_topc(A_1955) | v2_struct_0(A_1955) | ~m1_pre_topc(k1_tsep_1(A_1955, '#skF_6', '#skF_5'), '#skF_6') | ~l1_pre_topc(k1_tsep_1(A_1955, '#skF_6', '#skF_5')) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_86123])).
% 45.26/32.24  tff(c_86139, plain, (![A_1956]: (~m1_pre_topc('#skF_5', A_1956) | ~m1_pre_topc('#skF_6', A_1956) | ~l1_pre_topc(A_1956) | v2_struct_0(A_1956) | ~m1_pre_topc(k1_tsep_1(A_1956, '#skF_6', '#skF_5'), '#skF_6') | ~l1_pre_topc(k1_tsep_1(A_1956, '#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_86133])).
% 45.26/32.24  tff(c_86143, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_58, c_86139])).
% 45.26/32.24  tff(c_86146, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_6', '#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_570, c_74, c_86143])).
% 45.26/32.24  tff(c_86147, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_86, c_86146])).
% 45.26/32.24  tff(c_86150, plain, (~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_794, c_86147])).
% 45.26/32.24  tff(c_86153, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_570, c_74, c_86150])).
% 45.26/32.24  tff(c_86155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_86, c_86153])).
% 45.26/32.24  tff(c_86157, plain, (r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_635])).
% 45.26/32.24  tff(c_64, plain, (![B_76, A_75]: (r1_tsep_1(B_76, A_75) | ~r1_tsep_1(A_75, B_76) | ~l1_struct_0(B_76) | ~l1_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_155])).
% 45.26/32.24  tff(c_86159, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86157, c_64])).
% 45.26/32.24  tff(c_86162, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_418, c_86159])).
% 45.26/32.24  tff(c_86164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_86162])).
% 45.26/32.24  tff(c_86166, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 45.26/32.24  tff(c_86165, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 45.26/32.24  tff(c_86281, plain, (![B_1979, A_1980]: (r1_tsep_1(B_1979, A_1980) | ~r1_tsep_1(A_1980, B_1979) | ~l1_struct_0(B_1979) | ~l1_struct_0(A_1980))), inference(cnfTransformation, [status(thm)], [f_155])).
% 45.26/32.24  tff(c_86283, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86165, c_86281])).
% 45.26/32.24  tff(c_86286, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_86166, c_86283])).
% 45.26/32.24  tff(c_86287, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_86286])).
% 45.26/32.24  tff(c_86290, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_86287])).
% 45.26/32.24  tff(c_86294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86196, c_86290])).
% 45.26/32.24  tff(c_86295, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_86286])).
% 45.26/32.24  tff(c_86304, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_46, c_86295])).
% 45.26/32.24  tff(c_86308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86220, c_86304])).
% 45.26/32.24  tff(c_86309, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 45.26/32.24  tff(c_86310, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 45.26/32.24  tff(c_86408, plain, (![B_2001, A_2002]: (r1_tsep_1(B_2001, A_2002) | ~r1_tsep_1(A_2002, B_2001) | ~l1_struct_0(B_2001) | ~l1_struct_0(A_2002))), inference(cnfTransformation, [status(thm)], [f_155])).
% 45.26/32.24  tff(c_86412, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_86310, c_86408])).
% 45.26/32.24  tff(c_86416, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86309, c_86412])).
% 45.26/32.24  tff(c_86417, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_86416])).
% 45.26/32.24  tff(c_86420, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_86417])).
% 45.26/32.24  tff(c_86424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86335, c_86420])).
% 45.26/32.24  tff(c_86425, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_86416])).
% 45.26/32.24  tff(c_86429, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_86425])).
% 45.26/32.24  tff(c_86433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86332, c_86429])).
% 45.26/32.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.26/32.24  
% 45.26/32.24  Inference rules
% 45.26/32.24  ----------------------
% 45.26/32.24  #Ref     : 2
% 45.26/32.24  #Sup     : 23321
% 45.26/32.24  #Fact    : 2
% 45.26/32.24  #Define  : 0
% 45.26/32.24  #Split   : 93
% 45.26/32.24  #Chain   : 0
% 45.26/32.24  #Close   : 0
% 45.26/32.24  
% 45.26/32.24  Ordering : KBO
% 45.26/32.24  
% 45.26/32.24  Simplification rules
% 45.26/32.24  ----------------------
% 45.26/32.24  #Subsume      : 5758
% 45.26/32.24  #Demod        : 7398
% 45.26/32.24  #Tautology    : 2190
% 45.26/32.24  #SimpNegUnit  : 5650
% 45.26/32.24  #BackRed      : 408
% 45.26/32.24  
% 45.26/32.24  #Partial instantiations: 0
% 45.26/32.24  #Strategies tried      : 1
% 45.26/32.24  
% 45.26/32.24  Timing (in seconds)
% 45.26/32.24  ----------------------
% 45.26/32.25  Preprocessing        : 0.43
% 45.26/32.25  Parsing              : 0.19
% 45.26/32.25  CNF conversion       : 0.04
% 45.26/32.25  Main loop            : 31.00
% 45.26/32.25  Inferencing          : 4.42
% 45.26/32.25  Reduction            : 8.50
% 45.26/32.25  Demodulation         : 6.26
% 45.26/32.25  BG Simplification    : 0.55
% 45.26/32.25  Subsumption          : 15.90
% 45.26/32.25  Abstraction          : 0.69
% 45.26/32.25  MUC search           : 0.00
% 45.26/32.25  Cooper               : 0.00
% 45.26/32.25  Total                : 31.49
% 45.26/32.25  Index Insertion      : 0.00
% 45.26/32.25  Index Deletion       : 0.00
% 45.26/32.25  Index Matching       : 0.00
% 45.26/32.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
