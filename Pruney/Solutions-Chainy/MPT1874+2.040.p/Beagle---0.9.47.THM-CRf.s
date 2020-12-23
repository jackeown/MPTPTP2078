%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 163 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 467 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,
    ( m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_89,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_125,plain,(
    ! [B_55,A_56,A_57] :
      ( ~ v1_xboole_0(B_55)
      | ~ r2_hidden(A_56,A_57)
      | ~ r1_tarski(A_57,B_55) ) ),
    inference(resolution,[status(thm)],[c_18,c_113])).

tff(c_135,plain,(
    ! [B_58] :
      ( ~ v1_xboole_0(B_58)
      | ~ r1_tarski('#skF_4',B_58) ) ),
    inference(resolution,[status(thm)],[c_36,c_125])).

tff(c_139,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_135])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_139])).

tff(c_148,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_147,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_257,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(A_88,B_89) = k1_tarski(B_89)
      | ~ m1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_260,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_147,c_257])).

tff(c_275,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_260])).

tff(c_363,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(k6_domain_1(A_95,B_96),k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_383,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_363])).

tff(c_395,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_383])).

tff(c_396,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_395])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_410,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_396,c_16])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_49,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_58,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_272,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_283,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_272])).

tff(c_380,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_363])).

tff(c_392,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_380])).

tff(c_393,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_392])).

tff(c_823,plain,(
    ! [A_129,B_130,C_131] :
      ( k9_subset_1(u1_struct_0(A_129),B_130,k2_pre_topc(A_129,C_131)) = C_131
      | ~ r1_tarski(C_131,B_130)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v2_tex_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_830,plain,(
    ! [B_130] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_130,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_130)
      | ~ v2_tex_2(B_130,'#skF_3')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_393,c_823])).

tff(c_846,plain,(
    ! [B_130] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_130,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_130)
      | ~ v2_tex_2(B_130,'#skF_3')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_830])).

tff(c_1233,plain,(
    ! [B_141] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_141,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_141)
      | ~ v2_tex_2(B_141,'#skF_3')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_846])).

tff(c_34,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_288,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_283,c_34])).

tff(c_1239,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1233,c_288])).

tff(c_1247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_410,c_1239])).

tff(c_1249,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_1335,plain,(
    ! [C_166,B_167,A_168] :
      ( ~ v1_xboole_0(C_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(C_166))
      | ~ r2_hidden(A_168,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1342,plain,(
    ! [A_168] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_168,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_1335])).

tff(c_1347,plain,(
    ! [A_168] : ~ r2_hidden(A_168,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1342])).

tff(c_1349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1347,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.59  
% 3.36/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.59  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.36/1.59  
% 3.36/1.59  %Foreground sorts:
% 3.36/1.59  
% 3.36/1.59  
% 3.36/1.59  %Background operators:
% 3.36/1.59  
% 3.36/1.59  
% 3.36/1.59  %Foreground operators:
% 3.36/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.36/1.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.36/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.59  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.36/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.36/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.36/1.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.36/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.59  
% 3.36/1.61  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.36/1.61  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.36/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.36/1.61  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.36/1.61  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.36/1.61  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.36/1.61  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.36/1.61  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.36/1.61  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_84, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.61  tff(c_88, plain, (m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_84])).
% 3.36/1.61  tff(c_89, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_88])).
% 3.36/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.61  tff(c_100, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.61  tff(c_110, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_100])).
% 3.36/1.61  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.61  tff(c_113, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.61  tff(c_125, plain, (![B_55, A_56, A_57]: (~v1_xboole_0(B_55) | ~r2_hidden(A_56, A_57) | ~r1_tarski(A_57, B_55))), inference(resolution, [status(thm)], [c_18, c_113])).
% 3.36/1.61  tff(c_135, plain, (![B_58]: (~v1_xboole_0(B_58) | ~r1_tarski('#skF_4', B_58))), inference(resolution, [status(thm)], [c_36, c_125])).
% 3.36/1.61  tff(c_139, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_110, c_135])).
% 3.36/1.61  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_139])).
% 3.36/1.61  tff(c_148, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_88])).
% 3.36/1.61  tff(c_147, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_88])).
% 3.36/1.61  tff(c_257, plain, (![A_88, B_89]: (k6_domain_1(A_88, B_89)=k1_tarski(B_89) | ~m1_subset_1(B_89, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.36/1.61  tff(c_260, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_147, c_257])).
% 3.36/1.61  tff(c_275, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_148, c_260])).
% 3.36/1.61  tff(c_363, plain, (![A_95, B_96]: (m1_subset_1(k6_domain_1(A_95, B_96), k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.61  tff(c_383, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_275, c_363])).
% 3.36/1.61  tff(c_395, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_383])).
% 3.36/1.61  tff(c_396, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_148, c_395])).
% 3.36/1.61  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.61  tff(c_410, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_396, c_16])).
% 3.36/1.61  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_49, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.61  tff(c_57, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 3.36/1.61  tff(c_58, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_57])).
% 3.36/1.61  tff(c_272, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_257])).
% 3.36/1.61  tff(c_283, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_272])).
% 3.36/1.61  tff(c_380, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_363])).
% 3.36/1.61  tff(c_392, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_380])).
% 3.36/1.61  tff(c_393, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_392])).
% 3.36/1.61  tff(c_823, plain, (![A_129, B_130, C_131]: (k9_subset_1(u1_struct_0(A_129), B_130, k2_pre_topc(A_129, C_131))=C_131 | ~r1_tarski(C_131, B_130) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_129))) | ~v2_tex_2(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.61  tff(c_830, plain, (![B_130]: (k9_subset_1(u1_struct_0('#skF_3'), B_130, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_130) | ~v2_tex_2(B_130, '#skF_3') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_393, c_823])).
% 3.36/1.61  tff(c_846, plain, (![B_130]: (k9_subset_1(u1_struct_0('#skF_3'), B_130, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_130) | ~v2_tex_2(B_130, '#skF_3') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_830])).
% 3.36/1.61  tff(c_1233, plain, (![B_141]: (k9_subset_1(u1_struct_0('#skF_3'), B_141, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_141) | ~v2_tex_2(B_141, '#skF_3') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_846])).
% 3.36/1.61  tff(c_34, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.61  tff(c_288, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_283, c_34])).
% 3.36/1.61  tff(c_1239, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1233, c_288])).
% 3.36/1.61  tff(c_1247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_410, c_1239])).
% 3.36/1.61  tff(c_1249, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_57])).
% 3.36/1.61  tff(c_1335, plain, (![C_166, B_167, A_168]: (~v1_xboole_0(C_166) | ~m1_subset_1(B_167, k1_zfmisc_1(C_166)) | ~r2_hidden(A_168, B_167))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.61  tff(c_1342, plain, (![A_168]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_168, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_1335])).
% 3.36/1.61  tff(c_1347, plain, (![A_168]: (~r2_hidden(A_168, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1342])).
% 3.36/1.61  tff(c_1349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1347, c_36])).
% 3.36/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.61  
% 3.36/1.61  Inference rules
% 3.36/1.61  ----------------------
% 3.36/1.61  #Ref     : 0
% 3.36/1.61  #Sup     : 291
% 3.36/1.61  #Fact    : 0
% 3.36/1.61  #Define  : 0
% 3.36/1.61  #Split   : 13
% 3.36/1.61  #Chain   : 0
% 3.36/1.61  #Close   : 0
% 3.36/1.61  
% 3.36/1.61  Ordering : KBO
% 3.36/1.61  
% 3.36/1.61  Simplification rules
% 3.36/1.61  ----------------------
% 3.36/1.61  #Subsume      : 79
% 3.36/1.61  #Demod        : 75
% 3.36/1.61  #Tautology    : 76
% 3.36/1.61  #SimpNegUnit  : 55
% 3.36/1.61  #BackRed      : 2
% 3.36/1.61  
% 3.36/1.61  #Partial instantiations: 0
% 3.36/1.61  #Strategies tried      : 1
% 3.36/1.61  
% 3.36/1.61  Timing (in seconds)
% 3.36/1.61  ----------------------
% 3.36/1.61  Preprocessing        : 0.33
% 3.36/1.61  Parsing              : 0.18
% 3.36/1.61  CNF conversion       : 0.02
% 3.36/1.61  Main loop            : 0.44
% 3.36/1.61  Inferencing          : 0.16
% 3.36/1.61  Reduction            : 0.13
% 3.36/1.61  Demodulation         : 0.09
% 3.36/1.61  BG Simplification    : 0.02
% 3.36/1.61  Subsumption          : 0.09
% 3.36/1.61  Abstraction          : 0.02
% 3.36/1.61  MUC search           : 0.00
% 3.36/1.61  Cooper               : 0.00
% 3.36/1.61  Total                : 0.81
% 3.36/1.61  Index Insertion      : 0.00
% 3.36/1.61  Index Deletion       : 0.00
% 3.36/1.61  Index Matching       : 0.00
% 3.36/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
