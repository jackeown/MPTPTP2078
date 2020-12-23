%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   65 (  82 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 248 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_22,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = k1_xboole_0
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_orders_2(A_40) ) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_62,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_30,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_63,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30])).

tff(c_40,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_87,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_1,B_2,B_49] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_49)
      | ~ r1_tarski(A_1,B_49)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_130,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k3_orders_2(A_64,B_65,C_66),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_172,plain,(
    ! [A_80,A_81,B_82,C_83] :
      ( m1_subset_1(A_80,u1_struct_0(A_81))
      | ~ r2_hidden(A_80,k3_orders_2(A_81,B_82,C_83))
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_130,c_14])).

tff(c_190,plain,(
    ! [C_89,A_88,B_92,A_91,B_90] :
      ( m1_subset_1('#skF_1'(A_91,B_90),u1_struct_0(A_88))
      | ~ m1_subset_1(C_89,u1_struct_0(A_88))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88)
      | ~ r1_tarski(A_91,k3_orders_2(A_88,B_92,C_89))
      | r1_tarski(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_90,c_172])).

tff(c_198,plain,(
    ! [A_93,B_94,A_95,C_96] :
      ( m1_subset_1('#skF_1'(A_93,B_94),u1_struct_0(A_95))
      | ~ m1_subset_1(C_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95)
      | ~ r1_tarski(A_93,k3_orders_2(A_95,k1_xboole_0,C_96))
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_12,c_190])).

tff(c_205,plain,(
    ! [A_95,C_96,B_94] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_95,k1_xboole_0,C_96),B_94),u1_struct_0(A_95))
      | ~ m1_subset_1(C_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95)
      | r1_tarski(k3_orders_2(A_95,k1_xboole_0,C_96),B_94) ) ),
    inference(resolution,[status(thm)],[c_79,c_198])).

tff(c_163,plain,(
    ! [B_76,D_77,A_78,C_79] :
      ( r2_hidden(B_76,D_77)
      | ~ r2_hidden(B_76,k3_orders_2(A_78,D_77,C_79))
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(C_79,u1_struct_0(A_78))
      | ~ m1_subset_1(B_76,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_281,plain,(
    ! [A_134,D_135,C_136,B_137] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_134,D_135,C_136),B_137),D_135)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(C_136,u1_struct_0(A_134))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_134,D_135,C_136),B_137),u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134)
      | r1_tarski(k3_orders_2(A_134,D_135,C_136),B_137) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_285,plain,(
    ! [A_95,C_96,B_94] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_95,k1_xboole_0,C_96),B_94),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(C_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95)
      | r1_tarski(k3_orders_2(A_95,k1_xboole_0,C_96),B_94) ) ),
    inference(resolution,[status(thm)],[c_205,c_281])).

tff(c_290,plain,(
    ! [A_138,C_139,B_140] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_138,k1_xboole_0,C_139),B_140),k1_xboole_0)
      | ~ m1_subset_1(C_139,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138)
      | r1_tarski(k3_orders_2(A_138,k1_xboole_0,C_139),B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_285])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_310,plain,(
    ! [C_141,A_142] :
      ( ~ m1_subset_1(C_141,u1_struct_0(A_142))
      | ~ l1_orders_2(A_142)
      | ~ v5_orders_2(A_142)
      | ~ v4_orders_2(A_142)
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142)
      | r1_tarski(k3_orders_2(A_142,k1_xboole_0,C_141),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_290,c_4])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_328,plain,(
    ! [A_143,C_144] :
      ( k3_orders_2(A_143,k1_xboole_0,C_144) = k1_xboole_0
      | ~ m1_subset_1(C_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_310,c_10])).

tff(c_337,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_328])).

tff(c_342,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_337])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_63,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:37:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.36  
% 2.66/1.36  %Foreground sorts:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Background operators:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Foreground operators:
% 2.66/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.36  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.66/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.66/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.66/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.66/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.36  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.66/1.36  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.66/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.36  
% 2.66/1.37  tff(f_119, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 2.66/1.37  tff(f_76, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.66/1.37  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.66/1.37  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.66/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.37  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.66/1.37  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.66/1.37  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.66/1.37  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.66/1.37  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_34, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_22, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_53, plain, (![A_39]: (k1_struct_0(A_39)=k1_xboole_0 | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.37  tff(c_58, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_orders_2(A_40))), inference(resolution, [status(thm)], [c_22, c_53])).
% 2.66/1.37  tff(c_62, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.66/1.37  tff(c_30, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_63, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_30])).
% 2.66/1.37  tff(c_40, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_38, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_36, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.37  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_74, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_79, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_74])).
% 2.66/1.37  tff(c_87, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_90, plain, (![A_1, B_2, B_49]: (r2_hidden('#skF_1'(A_1, B_2), B_49) | ~r1_tarski(A_1, B_49) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.66/1.37  tff(c_130, plain, (![A_64, B_65, C_66]: (m1_subset_1(k3_orders_2(A_64, B_65, C_66), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.37  tff(c_14, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.37  tff(c_172, plain, (![A_80, A_81, B_82, C_83]: (m1_subset_1(A_80, u1_struct_0(A_81)) | ~r2_hidden(A_80, k3_orders_2(A_81, B_82, C_83)) | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_130, c_14])).
% 2.66/1.37  tff(c_190, plain, (![C_89, A_88, B_92, A_91, B_90]: (m1_subset_1('#skF_1'(A_91, B_90), u1_struct_0(A_88)) | ~m1_subset_1(C_89, u1_struct_0(A_88)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88) | ~r1_tarski(A_91, k3_orders_2(A_88, B_92, C_89)) | r1_tarski(A_91, B_90))), inference(resolution, [status(thm)], [c_90, c_172])).
% 2.66/1.37  tff(c_198, plain, (![A_93, B_94, A_95, C_96]: (m1_subset_1('#skF_1'(A_93, B_94), u1_struct_0(A_95)) | ~m1_subset_1(C_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95) | ~r1_tarski(A_93, k3_orders_2(A_95, k1_xboole_0, C_96)) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_12, c_190])).
% 2.66/1.37  tff(c_205, plain, (![A_95, C_96, B_94]: (m1_subset_1('#skF_1'(k3_orders_2(A_95, k1_xboole_0, C_96), B_94), u1_struct_0(A_95)) | ~m1_subset_1(C_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95) | r1_tarski(k3_orders_2(A_95, k1_xboole_0, C_96), B_94))), inference(resolution, [status(thm)], [c_79, c_198])).
% 2.66/1.37  tff(c_163, plain, (![B_76, D_77, A_78, C_79]: (r2_hidden(B_76, D_77) | ~r2_hidden(B_76, k3_orders_2(A_78, D_77, C_79)) | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(C_79, u1_struct_0(A_78)) | ~m1_subset_1(B_76, u1_struct_0(A_78)) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.66/1.37  tff(c_281, plain, (![A_134, D_135, C_136, B_137]: (r2_hidden('#skF_1'(k3_orders_2(A_134, D_135, C_136), B_137), D_135) | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(C_136, u1_struct_0(A_134)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_134, D_135, C_136), B_137), u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134) | r1_tarski(k3_orders_2(A_134, D_135, C_136), B_137))), inference(resolution, [status(thm)], [c_6, c_163])).
% 2.66/1.37  tff(c_285, plain, (![A_95, C_96, B_94]: (r2_hidden('#skF_1'(k3_orders_2(A_95, k1_xboole_0, C_96), B_94), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(C_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95) | r1_tarski(k3_orders_2(A_95, k1_xboole_0, C_96), B_94))), inference(resolution, [status(thm)], [c_205, c_281])).
% 2.66/1.37  tff(c_290, plain, (![A_138, C_139, B_140]: (r2_hidden('#skF_1'(k3_orders_2(A_138, k1_xboole_0, C_139), B_140), k1_xboole_0) | ~m1_subset_1(C_139, u1_struct_0(A_138)) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138) | r1_tarski(k3_orders_2(A_138, k1_xboole_0, C_139), B_140))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_285])).
% 2.66/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_310, plain, (![C_141, A_142]: (~m1_subset_1(C_141, u1_struct_0(A_142)) | ~l1_orders_2(A_142) | ~v5_orders_2(A_142) | ~v4_orders_2(A_142) | ~v3_orders_2(A_142) | v2_struct_0(A_142) | r1_tarski(k3_orders_2(A_142, k1_xboole_0, C_141), k1_xboole_0))), inference(resolution, [status(thm)], [c_290, c_4])).
% 2.66/1.37  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.37  tff(c_328, plain, (![A_143, C_144]: (k3_orders_2(A_143, k1_xboole_0, C_144)=k1_xboole_0 | ~m1_subset_1(C_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v5_orders_2(A_143) | ~v4_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_310, c_10])).
% 2.66/1.37  tff(c_337, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_328])).
% 2.66/1.37  tff(c_342, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_337])).
% 2.66/1.37  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_63, c_342])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 64
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 0
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 7
% 2.66/1.37  #Demod        : 16
% 2.66/1.37  #Tautology    : 13
% 2.66/1.37  #SimpNegUnit  : 1
% 2.66/1.37  #BackRed      : 1
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.38  Preprocessing        : 0.30
% 2.66/1.38  Parsing              : 0.17
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.30
% 2.66/1.38  Inferencing          : 0.12
% 2.66/1.38  Reduction            : 0.07
% 2.66/1.38  Demodulation         : 0.05
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.08
% 2.66/1.38  Abstraction          : 0.01
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.64
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
