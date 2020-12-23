%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 108 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 275 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k4_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_96,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_1'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_155,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [B_55,A_56,A_57] :
      ( ~ v1_xboole_0(B_55)
      | ~ r2_hidden(A_56,A_57)
      | ~ r1_tarski(A_57,B_55) ) ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_163,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | ~ r1_tarski(A_59,B_58)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_188,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | k4_xboole_0(A_63,B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_191,plain,(
    ! [B_64] : k4_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_188])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_240,plain,(
    ! [B_76,A_77] :
      ( v2_tex_2(B_76,A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v1_xboole_0(B_76)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_251,plain,(
    ! [A_80,A_81] :
      ( v2_tex_2(A_80,A_81)
      | ~ v1_xboole_0(A_80)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ r1_tarski(A_80,u1_struct_0(A_81)) ) ),
    inference(resolution,[status(thm)],[c_12,c_240])).

tff(c_262,plain,(
    ! [A_82,A_83] :
      ( v2_tex_2(A_82,A_83)
      | ~ v1_xboole_0(A_82)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | k4_xboole_0(A_82,u1_struct_0(A_83)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_251])).

tff(c_266,plain,(
    ! [A_83] :
      ( v2_tex_2(k1_xboole_0,A_83)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_262])).

tff(c_273,plain,(
    ! [A_83] :
      ( v2_tex_2(k1_xboole_0,A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_266])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_276,plain,(
    ! [A_85,B_86] :
      ( v3_tex_2('#skF_2'(A_85,B_86),A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v3_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_280,plain,(
    ! [A_85,A_5] :
      ( v3_tex_2('#skF_2'(A_85,A_5),A_85)
      | ~ v2_tex_2(A_5,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ v3_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | ~ r1_tarski(A_5,u1_struct_0(A_85)) ) ),
    inference(resolution,[status(thm)],[c_12,c_276])).

tff(c_301,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1('#skF_2'(A_95,B_96),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v3_tdlat_3(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [B_30] :
      ( ~ v3_tex_2(B_30,'#skF_3')
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_317,plain,(
    ! [B_96] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_96),'#skF_3')
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_301,c_30])).

tff(c_325,plain,(
    ! [B_96] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_96),'#skF_3')
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_317])).

tff(c_327,plain,(
    ! [B_97] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_97),'#skF_3')
      | ~ v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_325])).

tff(c_341,plain,(
    ! [A_98] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',A_98),'#skF_3')
      | ~ v2_tex_2(A_98,'#skF_3')
      | ~ r1_tarski(A_98,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_327])).

tff(c_345,plain,(
    ! [A_5] :
      ( ~ v2_tex_2(A_5,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_280,c_341])).

tff(c_348,plain,(
    ! [A_5] :
      ( ~ v2_tex_2(A_5,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_345])).

tff(c_350,plain,(
    ! [A_99] :
      ( ~ v2_tex_2(A_99,'#skF_3')
      | ~ r1_tarski(A_99,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_348])).

tff(c_379,plain,(
    ! [A_103] :
      ( ~ v2_tex_2(A_103,'#skF_3')
      | k4_xboole_0(A_103,u1_struct_0('#skF_3')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_350])).

tff(c_388,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_379])).

tff(c_392,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_273,c_388])).

tff(c_395,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_392])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.59  
% 2.68/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.59  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k4_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.68/1.59  
% 2.68/1.59  %Foreground sorts:
% 2.68/1.59  
% 2.68/1.59  
% 2.68/1.59  %Background operators:
% 2.68/1.59  
% 2.68/1.59  
% 2.68/1.59  %Foreground operators:
% 2.68/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.68/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.59  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.68/1.59  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.68/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.59  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.68/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.59  
% 2.68/1.61  tff(f_111, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.68/1.61  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.61  tff(f_32, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.68/1.61  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.68/1.61  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.61  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.68/1.61  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.68/1.61  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.68/1.61  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.68/1.61  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.61  tff(c_36, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.61  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.61  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.61  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.61  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_1'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.61  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.61  tff(c_155, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.61  tff(c_159, plain, (![B_55, A_56, A_57]: (~v1_xboole_0(B_55) | ~r2_hidden(A_56, A_57) | ~r1_tarski(A_57, B_55))), inference(resolution, [status(thm)], [c_12, c_155])).
% 2.68/1.61  tff(c_163, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | ~r1_tarski(A_59, B_58) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_16, c_159])).
% 2.68/1.61  tff(c_188, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | k4_xboole_0(A_63, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_163])).
% 2.68/1.61  tff(c_191, plain, (![B_64]: (k4_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_188])).
% 2.68/1.61  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.61  tff(c_240, plain, (![B_76, A_77]: (v2_tex_2(B_76, A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~v1_xboole_0(B_76) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.61  tff(c_251, plain, (![A_80, A_81]: (v2_tex_2(A_80, A_81) | ~v1_xboole_0(A_80) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~r1_tarski(A_80, u1_struct_0(A_81)))), inference(resolution, [status(thm)], [c_12, c_240])).
% 2.68/1.61  tff(c_262, plain, (![A_82, A_83]: (v2_tex_2(A_82, A_83) | ~v1_xboole_0(A_82) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | k4_xboole_0(A_82, u1_struct_0(A_83))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_251])).
% 2.68/1.61  tff(c_266, plain, (![A_83]: (v2_tex_2(k1_xboole_0, A_83) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(superposition, [status(thm), theory('equality')], [c_191, c_262])).
% 2.68/1.61  tff(c_273, plain, (![A_83]: (v2_tex_2(k1_xboole_0, A_83) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_266])).
% 2.68/1.61  tff(c_34, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.61  tff(c_276, plain, (![A_85, B_86]: (v3_tex_2('#skF_2'(A_85, B_86), A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v3_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.61  tff(c_280, plain, (![A_85, A_5]: (v3_tex_2('#skF_2'(A_85, A_5), A_85) | ~v2_tex_2(A_5, A_85) | ~l1_pre_topc(A_85) | ~v3_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | ~r1_tarski(A_5, u1_struct_0(A_85)))), inference(resolution, [status(thm)], [c_12, c_276])).
% 2.68/1.61  tff(c_301, plain, (![A_95, B_96]: (m1_subset_1('#skF_2'(A_95, B_96), k1_zfmisc_1(u1_struct_0(A_95))) | ~v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v3_tdlat_3(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.61  tff(c_30, plain, (![B_30]: (~v3_tex_2(B_30, '#skF_3') | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.61  tff(c_317, plain, (![B_96]: (~v3_tex_2('#skF_2'('#skF_3', B_96), '#skF_3') | ~v2_tex_2(B_96, '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_301, c_30])).
% 2.68/1.61  tff(c_325, plain, (![B_96]: (~v3_tex_2('#skF_2'('#skF_3', B_96), '#skF_3') | ~v2_tex_2(B_96, '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_317])).
% 2.68/1.61  tff(c_327, plain, (![B_97]: (~v3_tex_2('#skF_2'('#skF_3', B_97), '#skF_3') | ~v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_325])).
% 2.68/1.61  tff(c_341, plain, (![A_98]: (~v3_tex_2('#skF_2'('#skF_3', A_98), '#skF_3') | ~v2_tex_2(A_98, '#skF_3') | ~r1_tarski(A_98, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_327])).
% 2.68/1.61  tff(c_345, plain, (![A_5]: (~v2_tex_2(A_5, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_280, c_341])).
% 2.68/1.61  tff(c_348, plain, (![A_5]: (~v2_tex_2(A_5, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_345])).
% 2.68/1.61  tff(c_350, plain, (![A_99]: (~v2_tex_2(A_99, '#skF_3') | ~r1_tarski(A_99, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_348])).
% 2.68/1.61  tff(c_379, plain, (![A_103]: (~v2_tex_2(A_103, '#skF_3') | k4_xboole_0(A_103, u1_struct_0('#skF_3'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_350])).
% 2.68/1.61  tff(c_388, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_191, c_379])).
% 2.68/1.61  tff(c_392, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_273, c_388])).
% 2.68/1.61  tff(c_395, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_392])).
% 2.68/1.61  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_395])).
% 2.68/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.61  
% 2.68/1.61  Inference rules
% 2.68/1.61  ----------------------
% 2.68/1.61  #Ref     : 0
% 2.68/1.61  #Sup     : 74
% 2.68/1.61  #Fact    : 0
% 2.68/1.61  #Define  : 0
% 2.68/1.61  #Split   : 0
% 2.68/1.61  #Chain   : 0
% 2.68/1.61  #Close   : 0
% 2.68/1.61  
% 2.68/1.61  Ordering : KBO
% 2.68/1.61  
% 2.68/1.61  Simplification rules
% 2.68/1.61  ----------------------
% 2.68/1.61  #Subsume      : 5
% 2.68/1.61  #Demod        : 36
% 2.68/1.61  #Tautology    : 31
% 2.68/1.61  #SimpNegUnit  : 6
% 2.68/1.61  #BackRed      : 0
% 2.68/1.61  
% 2.68/1.61  #Partial instantiations: 0
% 2.68/1.61  #Strategies tried      : 1
% 2.68/1.61  
% 2.68/1.61  Timing (in seconds)
% 2.68/1.61  ----------------------
% 2.68/1.61  Preprocessing        : 0.42
% 2.68/1.61  Parsing              : 0.25
% 2.68/1.61  CNF conversion       : 0.03
% 2.68/1.61  Main loop            : 0.30
% 2.68/1.61  Inferencing          : 0.13
% 2.68/1.61  Reduction            : 0.08
% 2.68/1.61  Demodulation         : 0.06
% 2.68/1.61  BG Simplification    : 0.02
% 2.68/1.61  Subsumption          : 0.06
% 2.68/1.61  Abstraction          : 0.01
% 2.68/1.61  MUC search           : 0.00
% 2.68/1.61  Cooper               : 0.00
% 2.68/1.61  Total                : 0.76
% 2.68/1.61  Index Insertion      : 0.00
% 2.68/1.61  Index Deletion       : 0.00
% 2.68/1.61  Index Matching       : 0.00
% 2.68/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
