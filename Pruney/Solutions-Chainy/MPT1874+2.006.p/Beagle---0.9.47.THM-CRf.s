%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:37 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 169 expanded)
%              Number of leaves         :   33 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 475 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden('#skF_2'(A_54,B_55),B_55)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_155,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_6',B_68)
      | ~ r1_tarski('#skF_5',B_68) ) ),
    inference(resolution,[status(thm)],[c_38,c_155])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ! [B_72,B_73] :
      ( r2_hidden('#skF_6',B_72)
      | ~ r1_tarski(B_73,B_72)
      | ~ r1_tarski('#skF_5',B_73) ) ),
    inference(resolution,[status(thm)],[c_168,c_6])).

tff(c_207,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_75,c_199])).

tff(c_213,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_207])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_781,plain,(
    ! [A_139,B_140,C_141] :
      ( k9_subset_1(u1_struct_0(A_139),B_140,k2_pre_topc(A_139,C_141)) = C_141
      | ~ r1_tarski(C_141,B_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ v2_tex_2(B_140,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1812,plain,(
    ! [A_201,B_202,A_203] :
      ( k9_subset_1(u1_struct_0(A_201),B_202,k2_pre_topc(A_201,A_203)) = A_203
      | ~ r1_tarski(A_203,B_202)
      | ~ v2_tex_2(B_202,A_201)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201)
      | ~ r1_tarski(A_203,u1_struct_0(A_201)) ) ),
    inference(resolution,[status(thm)],[c_24,c_781])).

tff(c_1819,plain,(
    ! [A_203] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_203)) = A_203
      | ~ r1_tarski(A_203,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_203,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1812])).

tff(c_1824,plain,(
    ! [A_203] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_203)) = A_203
      | ~ r1_tarski(A_203,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_203,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_1819])).

tff(c_1949,plain,(
    ! [A_209] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_209)) = A_209
      | ~ r1_tarski(A_209,'#skF_5')
      | ~ r1_tarski(A_209,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1824])).

tff(c_51,plain,(
    ! [B_36,A_37] :
      ( ~ r2_hidden(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_116,plain,(
    ! [B_59,A_60] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_116])).

tff(c_126,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_122])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_233,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_242,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_233])).

tff(c_247,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_242])).

tff(c_36,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_248,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_247,c_36])).

tff(c_1977,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1949,c_248])).

tff(c_1982,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1977])).

tff(c_1991,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_1982])).

tff(c_1997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_1991])).

tff(c_1998,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1977])).

tff(c_2005,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1998])).

tff(c_2010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.30/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.85  
% 4.30/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.85  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.30/1.85  
% 4.30/1.85  %Foreground sorts:
% 4.30/1.85  
% 4.30/1.85  
% 4.30/1.85  %Background operators:
% 4.30/1.85  
% 4.30/1.85  
% 4.30/1.85  %Foreground operators:
% 4.30/1.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.30/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.30/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.30/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.30/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.30/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.30/1.85  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.30/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.30/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.30/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.30/1.85  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.30/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.30/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.30/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.30/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.30/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.30/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.30/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.30/1.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.30/1.85  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.30/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.30/1.85  
% 4.30/1.87  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 4.30/1.87  tff(f_46, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.30/1.87  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.30/1.87  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.30/1.87  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.30/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.30/1.87  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.30/1.87  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.30/1.87  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.87  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.30/1.87  tff(c_98, plain, (![A_54, B_55]: (~r2_hidden('#skF_2'(A_54, B_55), B_55) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.30/1.87  tff(c_103, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_98])).
% 4.30/1.87  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_71, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.30/1.87  tff(c_75, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_71])).
% 4.30/1.87  tff(c_155, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.30/1.87  tff(c_168, plain, (![B_68]: (r2_hidden('#skF_6', B_68) | ~r1_tarski('#skF_5', B_68))), inference(resolution, [status(thm)], [c_38, c_155])).
% 4.30/1.87  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.30/1.87  tff(c_199, plain, (![B_72, B_73]: (r2_hidden('#skF_6', B_72) | ~r1_tarski(B_73, B_72) | ~r1_tarski('#skF_5', B_73))), inference(resolution, [status(thm)], [c_168, c_6])).
% 4.30/1.87  tff(c_207, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_75, c_199])).
% 4.30/1.87  tff(c_213, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_207])).
% 4.30/1.87  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_42, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.30/1.87  tff(c_781, plain, (![A_139, B_140, C_141]: (k9_subset_1(u1_struct_0(A_139), B_140, k2_pre_topc(A_139, C_141))=C_141 | ~r1_tarski(C_141, B_140) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(A_139))) | ~v2_tex_2(B_140, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.30/1.87  tff(c_1812, plain, (![A_201, B_202, A_203]: (k9_subset_1(u1_struct_0(A_201), B_202, k2_pre_topc(A_201, A_203))=A_203 | ~r1_tarski(A_203, B_202) | ~v2_tex_2(B_202, A_201) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201) | ~r1_tarski(A_203, u1_struct_0(A_201)))), inference(resolution, [status(thm)], [c_24, c_781])).
% 4.30/1.87  tff(c_1819, plain, (![A_203]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_203))=A_203 | ~r1_tarski(A_203, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_203, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_44, c_1812])).
% 4.30/1.87  tff(c_1824, plain, (![A_203]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_203))=A_203 | ~r1_tarski(A_203, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_203, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_1819])).
% 4.30/1.87  tff(c_1949, plain, (![A_209]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_209))=A_209 | ~r1_tarski(A_209, '#skF_5') | ~r1_tarski(A_209, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1824])).
% 4.30/1.87  tff(c_51, plain, (![B_36, A_37]: (~r2_hidden(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.87  tff(c_55, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_51])).
% 4.30/1.87  tff(c_116, plain, (![B_59, A_60]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.87  tff(c_122, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_116])).
% 4.30/1.87  tff(c_126, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_122])).
% 4.30/1.87  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_233, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.30/1.87  tff(c_242, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_233])).
% 4.30/1.87  tff(c_247, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_126, c_242])).
% 4.30/1.87  tff(c_36, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.87  tff(c_248, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_247, c_36])).
% 4.30/1.87  tff(c_1977, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1949, c_248])).
% 4.30/1.87  tff(c_1982, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1977])).
% 4.30/1.87  tff(c_1991, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_1982])).
% 4.30/1.87  tff(c_1997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_1991])).
% 4.30/1.87  tff(c_1998, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_1977])).
% 4.30/1.87  tff(c_2005, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_18, c_1998])).
% 4.30/1.87  tff(c_2010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_2005])).
% 4.30/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.87  
% 4.30/1.87  Inference rules
% 4.30/1.87  ----------------------
% 4.30/1.87  #Ref     : 0
% 4.30/1.87  #Sup     : 501
% 4.30/1.87  #Fact    : 0
% 4.30/1.87  #Define  : 0
% 4.30/1.87  #Split   : 5
% 4.30/1.87  #Chain   : 0
% 4.30/1.87  #Close   : 0
% 4.30/1.87  
% 4.30/1.87  Ordering : KBO
% 4.30/1.87  
% 4.30/1.87  Simplification rules
% 4.30/1.87  ----------------------
% 4.30/1.87  #Subsume      : 126
% 4.30/1.87  #Demod        : 63
% 4.30/1.87  #Tautology    : 52
% 4.30/1.87  #SimpNegUnit  : 22
% 4.30/1.87  #BackRed      : 1
% 4.30/1.87  
% 4.30/1.87  #Partial instantiations: 0
% 4.30/1.87  #Strategies tried      : 1
% 4.30/1.87  
% 4.30/1.87  Timing (in seconds)
% 4.30/1.87  ----------------------
% 4.30/1.87  Preprocessing        : 0.35
% 4.30/1.87  Parsing              : 0.19
% 4.30/1.87  CNF conversion       : 0.03
% 4.30/1.87  Main loop            : 0.68
% 4.30/1.87  Inferencing          : 0.22
% 4.30/1.87  Reduction            : 0.19
% 4.30/1.87  Demodulation         : 0.12
% 4.30/1.87  BG Simplification    : 0.03
% 4.30/1.87  Subsumption          : 0.19
% 4.30/1.87  Abstraction          : 0.03
% 4.30/1.87  MUC search           : 0.00
% 4.30/1.87  Cooper               : 0.00
% 4.30/1.87  Total                : 1.07
% 4.30/1.87  Index Insertion      : 0.00
% 4.30/1.87  Index Deletion       : 0.00
% 4.30/1.87  Index Matching       : 0.00
% 4.30/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
