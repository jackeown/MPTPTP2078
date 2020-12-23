%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:36 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 136 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 345 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_19] :
      ( r2_hidden(u1_struct_0(A_19),u1_pre_topc(A_19))
      | ~ v2_pre_topc(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_135,plain,(
    ! [C_60,B_61,A_62] :
      ( r1_tarski(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(k3_tarski(A_62),B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_362,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(u1_struct_0(A_102),B_103)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(A_102)),B_103)
      | ~ v2_pre_topc(A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_62,c_135])).

tff(c_383,plain,(
    ! [A_105] :
      ( r1_tarski(u1_struct_0(A_105),k3_tarski(u1_pre_topc(A_105)))
      | ~ v2_pre_topc(A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_362])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( m1_setfam_1(B_6,A_5)
      | ~ r1_tarski(A_5,k3_tarski(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_393,plain,(
    ! [A_105] :
      ( m1_setfam_1(u1_pre_topc(A_105),u1_struct_0(A_105))
      | ~ v2_pre_topc(A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_383,c_12])).

tff(c_64,plain,(
    ! [A_33] :
      ( m1_subset_1(u1_pre_topc(A_33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33))))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_214,plain,(
    ! [A_78,B_79] :
      ( k5_setfam_1(A_78,B_79) = A_78
      | ~ m1_setfam_1(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_647,plain,(
    ! [A_132] :
      ( k5_setfam_1(u1_struct_0(A_132),u1_pre_topc(A_132)) = u1_struct_0(A_132)
      | ~ m1_setfam_1(u1_pre_topc(A_132),u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_64,c_214])).

tff(c_676,plain,(
    ! [A_134] :
      ( k5_setfam_1(u1_struct_0(A_134),u1_pre_topc(A_134)) = u1_struct_0(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_393,c_647])).

tff(c_139,plain,(
    ! [A_63,B_64] :
      ( k5_setfam_1(A_63,B_64) = k3_tarski(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_33] :
      ( k5_setfam_1(u1_struct_0(A_33),u1_pre_topc(A_33)) = k3_tarski(u1_pre_topc(A_33))
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_685,plain,(
    ! [A_134] :
      ( k3_tarski(u1_pre_topc(A_134)) = u1_struct_0(A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_147])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1226,plain,(
    ! [A_167] :
      ( k3_tarski(u1_pre_topc(A_167)) = u1_struct_0(A_167)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(A_167)),u1_struct_0(A_167))
      | ~ v2_pre_topc(A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_383,c_2])).

tff(c_1237,plain,(
    ! [A_134] :
      ( k3_tarski(u1_pre_topc(A_134)) = u1_struct_0(A_134)
      | ~ r1_tarski(u1_struct_0(A_134),u1_struct_0(A_134))
      | ~ v2_pre_topc(A_134)
      | ~ l1_pre_topc(A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_1226])).

tff(c_1243,plain,(
    ! [A_134] :
      ( k3_tarski(u1_pre_topc(A_134)) = u1_struct_0(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1237])).

tff(c_571,plain,(
    ! [A_124,B_125] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_124),B_125),u1_pre_topc(A_124))
      | ~ r1_tarski(B_125,u1_pre_topc(A_124))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_124))))
      | ~ v2_pre_topc(A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_578,plain,(
    ! [A_33] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_33)),u1_pre_topc(A_33))
      | ~ r1_tarski(u1_pre_topc(A_33),u1_pre_topc(A_33))
      | ~ m1_subset_1(u1_pre_topc(A_33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33))))
      | ~ v2_pre_topc(A_33)
      | ~ l1_pre_topc(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_571])).

tff(c_1766,plain,(
    ! [A_206] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_206)),u1_pre_topc(A_206))
      | ~ m1_subset_1(u1_pre_topc(A_206),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_206))))
      | ~ v2_pre_topc(A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_578])).

tff(c_1775,plain,(
    ! [A_207] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_207)),u1_pre_topc(A_207))
      | ~ v2_pre_topc(A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_64,c_1766])).

tff(c_66,plain,(
    ! [A_34] :
      ( k4_yellow_0(k2_yellow_1(A_34)) = k3_tarski(A_34)
      | ~ r2_hidden(k3_tarski(A_34),A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1789,plain,(
    ! [A_208] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_208))) = k3_tarski(u1_pre_topc(A_208))
      | v1_xboole_0(u1_pre_topc(A_208))
      | ~ v2_pre_topc(A_208)
      | ~ l1_pre_topc(A_208) ) ),
    inference(resolution,[status(thm)],[c_1775,c_66])).

tff(c_68,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1795,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1789,c_68])).

tff(c_1801,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_1795])).

tff(c_1803,plain,(
    k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1801])).

tff(c_1806,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_1803])).

tff(c_1810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_1806])).

tff(c_1811,plain,(
    v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1801])).

tff(c_131,plain,(
    ! [A_59] :
      ( r2_hidden(u1_struct_0(A_59),u1_pre_topc(A_59))
      | ~ v2_pre_topc(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [C_51,B_52,A_53] :
      ( ~ v1_xboole_0(C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,(
    ! [B_10,A_53,A_9] :
      ( ~ v1_xboole_0(B_10)
      | ~ r2_hidden(A_53,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_197,plain,(
    ! [B_74,A_75] :
      ( ~ v1_xboole_0(B_74)
      | ~ r1_tarski(u1_pre_topc(A_75),B_74)
      | ~ v2_pre_topc(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_131,c_117])).

tff(c_211,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(u1_pre_topc(A_75))
      | ~ v2_pre_topc(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_197])).

tff(c_1820,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1811,c_211])).

tff(c_1824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_1820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.87  
% 4.57/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.87  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 4.57/1.87  
% 4.57/1.87  %Foreground sorts:
% 4.57/1.87  
% 4.57/1.87  
% 4.57/1.87  %Background operators:
% 4.57/1.87  
% 4.57/1.87  
% 4.57/1.87  %Foreground operators:
% 4.57/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.57/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.57/1.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.57/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.57/1.87  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.57/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.57/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/1.87  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 4.57/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.87  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.57/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.57/1.87  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 4.57/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.57/1.87  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.57/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.57/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.57/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.87  
% 4.57/1.88  tff(f_112, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 4.57/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.57/1.88  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 4.57/1.88  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 4.57/1.88  tff(f_39, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 4.57/1.88  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.57/1.88  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 4.57/1.88  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 4.57/1.88  tff(f_102, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 4.57/1.88  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.57/1.88  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.57/1.88  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.57/1.88  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.57/1.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.88  tff(c_62, plain, (![A_19]: (r2_hidden(u1_struct_0(A_19), u1_pre_topc(A_19)) | ~v2_pre_topc(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.57/1.88  tff(c_135, plain, (![C_60, B_61, A_62]: (r1_tarski(C_60, B_61) | ~r2_hidden(C_60, A_62) | ~r1_tarski(k3_tarski(A_62), B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.57/1.88  tff(c_362, plain, (![A_102, B_103]: (r1_tarski(u1_struct_0(A_102), B_103) | ~r1_tarski(k3_tarski(u1_pre_topc(A_102)), B_103) | ~v2_pre_topc(A_102) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_62, c_135])).
% 4.57/1.88  tff(c_383, plain, (![A_105]: (r1_tarski(u1_struct_0(A_105), k3_tarski(u1_pre_topc(A_105))) | ~v2_pre_topc(A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_6, c_362])).
% 4.57/1.88  tff(c_12, plain, (![B_6, A_5]: (m1_setfam_1(B_6, A_5) | ~r1_tarski(A_5, k3_tarski(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.57/1.88  tff(c_393, plain, (![A_105]: (m1_setfam_1(u1_pre_topc(A_105), u1_struct_0(A_105)) | ~v2_pre_topc(A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_383, c_12])).
% 4.57/1.88  tff(c_64, plain, (![A_33]: (m1_subset_1(u1_pre_topc(A_33), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33)))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.57/1.88  tff(c_214, plain, (![A_78, B_79]: (k5_setfam_1(A_78, B_79)=A_78 | ~m1_setfam_1(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.57/1.88  tff(c_647, plain, (![A_132]: (k5_setfam_1(u1_struct_0(A_132), u1_pre_topc(A_132))=u1_struct_0(A_132) | ~m1_setfam_1(u1_pre_topc(A_132), u1_struct_0(A_132)) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_64, c_214])).
% 4.57/1.88  tff(c_676, plain, (![A_134]: (k5_setfam_1(u1_struct_0(A_134), u1_pre_topc(A_134))=u1_struct_0(A_134) | ~v2_pre_topc(A_134) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_393, c_647])).
% 4.57/1.88  tff(c_139, plain, (![A_63, B_64]: (k5_setfam_1(A_63, B_64)=k3_tarski(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.57/1.88  tff(c_147, plain, (![A_33]: (k5_setfam_1(u1_struct_0(A_33), u1_pre_topc(A_33))=k3_tarski(u1_pre_topc(A_33)) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_64, c_139])).
% 4.57/1.88  tff(c_685, plain, (![A_134]: (k3_tarski(u1_pre_topc(A_134))=u1_struct_0(A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | ~l1_pre_topc(A_134))), inference(superposition, [status(thm), theory('equality')], [c_676, c_147])).
% 4.57/1.88  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.88  tff(c_1226, plain, (![A_167]: (k3_tarski(u1_pre_topc(A_167))=u1_struct_0(A_167) | ~r1_tarski(k3_tarski(u1_pre_topc(A_167)), u1_struct_0(A_167)) | ~v2_pre_topc(A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_383, c_2])).
% 4.57/1.88  tff(c_1237, plain, (![A_134]: (k3_tarski(u1_pre_topc(A_134))=u1_struct_0(A_134) | ~r1_tarski(u1_struct_0(A_134), u1_struct_0(A_134)) | ~v2_pre_topc(A_134) | ~l1_pre_topc(A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | ~l1_pre_topc(A_134))), inference(superposition, [status(thm), theory('equality')], [c_685, c_1226])).
% 4.57/1.88  tff(c_1243, plain, (![A_134]: (k3_tarski(u1_pre_topc(A_134))=u1_struct_0(A_134) | ~v2_pre_topc(A_134) | ~l1_pre_topc(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1237])).
% 4.57/1.88  tff(c_571, plain, (![A_124, B_125]: (r2_hidden(k5_setfam_1(u1_struct_0(A_124), B_125), u1_pre_topc(A_124)) | ~r1_tarski(B_125, u1_pre_topc(A_124)) | ~m1_subset_1(B_125, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_124)))) | ~v2_pre_topc(A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.57/1.88  tff(c_578, plain, (![A_33]: (r2_hidden(k3_tarski(u1_pre_topc(A_33)), u1_pre_topc(A_33)) | ~r1_tarski(u1_pre_topc(A_33), u1_pre_topc(A_33)) | ~m1_subset_1(u1_pre_topc(A_33), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33)))) | ~v2_pre_topc(A_33) | ~l1_pre_topc(A_33) | ~l1_pre_topc(A_33))), inference(superposition, [status(thm), theory('equality')], [c_147, c_571])).
% 4.57/1.88  tff(c_1766, plain, (![A_206]: (r2_hidden(k3_tarski(u1_pre_topc(A_206)), u1_pre_topc(A_206)) | ~m1_subset_1(u1_pre_topc(A_206), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_206)))) | ~v2_pre_topc(A_206) | ~l1_pre_topc(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_578])).
% 4.57/1.88  tff(c_1775, plain, (![A_207]: (r2_hidden(k3_tarski(u1_pre_topc(A_207)), u1_pre_topc(A_207)) | ~v2_pre_topc(A_207) | ~l1_pre_topc(A_207))), inference(resolution, [status(thm)], [c_64, c_1766])).
% 4.57/1.88  tff(c_66, plain, (![A_34]: (k4_yellow_0(k2_yellow_1(A_34))=k3_tarski(A_34) | ~r2_hidden(k3_tarski(A_34), A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.57/1.88  tff(c_1789, plain, (![A_208]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_208)))=k3_tarski(u1_pre_topc(A_208)) | v1_xboole_0(u1_pre_topc(A_208)) | ~v2_pre_topc(A_208) | ~l1_pre_topc(A_208))), inference(resolution, [status(thm)], [c_1775, c_66])).
% 4.57/1.88  tff(c_68, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4')))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.57/1.88  tff(c_1795, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1789, c_68])).
% 4.57/1.88  tff(c_1801, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_1795])).
% 4.57/1.88  tff(c_1803, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1801])).
% 4.57/1.88  tff(c_1806, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1243, c_1803])).
% 4.57/1.88  tff(c_1810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_1806])).
% 4.57/1.88  tff(c_1811, plain, (v1_xboole_0(u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_1801])).
% 4.57/1.88  tff(c_131, plain, (![A_59]: (r2_hidden(u1_struct_0(A_59), u1_pre_topc(A_59)) | ~v2_pre_topc(A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.57/1.88  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.57/1.88  tff(c_114, plain, (![C_51, B_52, A_53]: (~v1_xboole_0(C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.57/1.88  tff(c_117, plain, (![B_10, A_53, A_9]: (~v1_xboole_0(B_10) | ~r2_hidden(A_53, A_9) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_18, c_114])).
% 4.57/1.88  tff(c_197, plain, (![B_74, A_75]: (~v1_xboole_0(B_74) | ~r1_tarski(u1_pre_topc(A_75), B_74) | ~v2_pre_topc(A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_131, c_117])).
% 4.57/1.88  tff(c_211, plain, (![A_75]: (~v1_xboole_0(u1_pre_topc(A_75)) | ~v2_pre_topc(A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_6, c_197])).
% 4.57/1.88  tff(c_1820, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1811, c_211])).
% 4.57/1.88  tff(c_1824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_1820])).
% 4.57/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.88  
% 4.57/1.88  Inference rules
% 4.57/1.88  ----------------------
% 4.57/1.88  #Ref     : 0
% 4.57/1.88  #Sup     : 430
% 4.57/1.88  #Fact    : 0
% 4.57/1.88  #Define  : 0
% 4.57/1.88  #Split   : 1
% 4.57/1.88  #Chain   : 0
% 4.57/1.88  #Close   : 0
% 4.57/1.88  
% 4.57/1.88  Ordering : KBO
% 4.57/1.88  
% 4.57/1.88  Simplification rules
% 4.57/1.88  ----------------------
% 4.57/1.88  #Subsume      : 67
% 4.57/1.88  #Demod        : 43
% 4.57/1.88  #Tautology    : 70
% 4.57/1.88  #SimpNegUnit  : 0
% 4.57/1.88  #BackRed      : 0
% 4.57/1.88  
% 4.57/1.88  #Partial instantiations: 0
% 4.57/1.88  #Strategies tried      : 1
% 4.57/1.88  
% 4.57/1.88  Timing (in seconds)
% 4.57/1.88  ----------------------
% 4.57/1.89  Preprocessing        : 0.36
% 4.57/1.89  Parsing              : 0.18
% 4.57/1.89  CNF conversion       : 0.03
% 4.57/1.89  Main loop            : 0.73
% 4.57/1.89  Inferencing          : 0.26
% 4.57/1.89  Reduction            : 0.18
% 4.57/1.89  Demodulation         : 0.12
% 4.57/1.89  BG Simplification    : 0.04
% 4.57/1.89  Subsumption          : 0.20
% 4.57/1.89  Abstraction          : 0.04
% 4.57/1.89  MUC search           : 0.00
% 4.57/1.89  Cooper               : 0.00
% 4.57/1.89  Total                : 1.12
% 4.57/1.89  Index Insertion      : 0.00
% 4.57/1.89  Index Deletion       : 0.00
% 4.57/1.89  Index Matching       : 0.00
% 4.57/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
