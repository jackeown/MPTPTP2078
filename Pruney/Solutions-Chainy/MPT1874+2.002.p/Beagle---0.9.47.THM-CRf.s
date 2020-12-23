%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:37 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 114 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 282 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_102,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_50,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_132,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k1_tarski(A_64),k1_zfmisc_1(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_136,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_132,c_32])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_54,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_111,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_119,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_zfmisc_1(A_13),k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_227,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_244,plain,(
    ! [A_81,B_82,A_83] :
      ( m1_subset_1(A_81,B_82)
      | ~ r2_hidden(A_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_34,c_227])).

tff(c_321,plain,(
    ! [C_93,B_94,A_95] :
      ( m1_subset_1(C_93,B_94)
      | ~ r1_tarski(k1_zfmisc_1(A_95),B_94)
      | ~ r1_tarski(C_93,A_95) ) ),
    inference(resolution,[status(thm)],[c_12,c_244])).

tff(c_330,plain,(
    ! [C_98,B_99,A_100] :
      ( m1_subset_1(C_98,k1_zfmisc_1(B_99))
      | ~ r1_tarski(C_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_22,c_321])).

tff(c_632,plain,(
    ! [A_135,B_136,B_137] :
      ( m1_subset_1(k1_tarski(A_135),k1_zfmisc_1(B_136))
      | ~ r1_tarski(B_137,B_136)
      | ~ r2_hidden(A_135,B_137) ) ),
    inference(resolution,[status(thm)],[c_136,c_330])).

tff(c_655,plain,(
    ! [A_135] :
      ( m1_subset_1(k1_tarski(A_135),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(A_135,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_119,c_632])).

tff(c_971,plain,(
    ! [A_169,B_170,C_171] :
      ( k9_subset_1(u1_struct_0(A_169),B_170,k2_pre_topc(A_169,C_171)) = C_171
      | ~ r1_tarski(C_171,B_170)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ v2_tex_2(B_170,A_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_975,plain,(
    ! [B_170,A_135] :
      ( k9_subset_1(u1_struct_0('#skF_5'),B_170,k2_pre_topc('#skF_5',k1_tarski(A_135))) = k1_tarski(A_135)
      | ~ r1_tarski(k1_tarski(A_135),B_170)
      | ~ v2_tex_2(B_170,'#skF_5')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(A_135,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_655,c_971])).

tff(c_996,plain,(
    ! [B_170,A_135] :
      ( k9_subset_1(u1_struct_0('#skF_5'),B_170,k2_pre_topc('#skF_5',k1_tarski(A_135))) = k1_tarski(A_135)
      | ~ r1_tarski(k1_tarski(A_135),B_170)
      | ~ v2_tex_2(B_170,'#skF_5')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(A_135,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_975])).

tff(c_1501,plain,(
    ! [B_205,A_206] :
      ( k9_subset_1(u1_struct_0('#skF_5'),B_205,k2_pre_topc('#skF_5',k1_tarski(A_206))) = k1_tarski(A_206)
      | ~ r1_tarski(k1_tarski(A_206),B_205)
      | ~ v2_tex_2(B_205,'#skF_5')
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(A_206,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_996])).

tff(c_73,plain,(
    ! [B_46,A_47] :
      ( ~ r2_hidden(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_73])).

tff(c_138,plain,(
    ! [B_68,A_69] :
      ( v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_138])).

tff(c_152,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_147])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_153,plain,(
    ! [A_70,B_71] :
      ( k6_domain_1(A_70,B_71) = k1_tarski(B_71)
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_175,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_153])).

tff(c_196,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_175])).

tff(c_48,plain,(
    k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_197,plain,(
    k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_5',k1_tarski('#skF_7'))) != k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_48])).

tff(c_1507,plain,
    ( ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_197])).

tff(c_1514,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_1507])).

tff(c_1518,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_1514])).

tff(c_1522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.68  
% 3.93/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.69  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.93/1.69  
% 3.93/1.69  %Foreground sorts:
% 3.93/1.69  
% 3.93/1.69  
% 3.93/1.69  %Background operators:
% 3.93/1.69  
% 3.93/1.69  
% 3.93/1.69  %Foreground operators:
% 3.93/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.93/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.93/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.93/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.93/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.93/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.93/1.69  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.93/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.93/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.69  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.93/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.93/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.93/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.93/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.93/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.93/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.69  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.93/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.93/1.69  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.93/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.69  
% 3.93/1.70  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 3.93/1.70  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.93/1.70  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.93/1.70  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.93/1.70  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.93/1.70  tff(f_76, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.93/1.70  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.93/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.93/1.70  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.93/1.70  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.93/1.70  tff(c_50, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_132, plain, (![A_64, B_65]: (m1_subset_1(k1_tarski(A_64), k1_zfmisc_1(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.93/1.70  tff(c_32, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.93/1.70  tff(c_136, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_132, c_32])).
% 3.93/1.70  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_54, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_111, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.93/1.70  tff(c_119, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_111])).
% 3.93/1.70  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(k1_zfmisc_1(A_13), k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.93/1.70  tff(c_12, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.93/1.70  tff(c_34, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.93/1.70  tff(c_227, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.93/1.70  tff(c_244, plain, (![A_81, B_82, A_83]: (m1_subset_1(A_81, B_82) | ~r2_hidden(A_81, A_83) | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_34, c_227])).
% 3.93/1.70  tff(c_321, plain, (![C_93, B_94, A_95]: (m1_subset_1(C_93, B_94) | ~r1_tarski(k1_zfmisc_1(A_95), B_94) | ~r1_tarski(C_93, A_95))), inference(resolution, [status(thm)], [c_12, c_244])).
% 3.93/1.70  tff(c_330, plain, (![C_98, B_99, A_100]: (m1_subset_1(C_98, k1_zfmisc_1(B_99)) | ~r1_tarski(C_98, A_100) | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_22, c_321])).
% 3.93/1.70  tff(c_632, plain, (![A_135, B_136, B_137]: (m1_subset_1(k1_tarski(A_135), k1_zfmisc_1(B_136)) | ~r1_tarski(B_137, B_136) | ~r2_hidden(A_135, B_137))), inference(resolution, [status(thm)], [c_136, c_330])).
% 3.93/1.70  tff(c_655, plain, (![A_135]: (m1_subset_1(k1_tarski(A_135), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(A_135, '#skF_6'))), inference(resolution, [status(thm)], [c_119, c_632])).
% 3.93/1.70  tff(c_971, plain, (![A_169, B_170, C_171]: (k9_subset_1(u1_struct_0(A_169), B_170, k2_pre_topc(A_169, C_171))=C_171 | ~r1_tarski(C_171, B_170) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_169))) | ~v2_tex_2(B_170, A_169) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.93/1.70  tff(c_975, plain, (![B_170, A_135]: (k9_subset_1(u1_struct_0('#skF_5'), B_170, k2_pre_topc('#skF_5', k1_tarski(A_135)))=k1_tarski(A_135) | ~r1_tarski(k1_tarski(A_135), B_170) | ~v2_tex_2(B_170, '#skF_5') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(A_135, '#skF_6'))), inference(resolution, [status(thm)], [c_655, c_971])).
% 3.93/1.70  tff(c_996, plain, (![B_170, A_135]: (k9_subset_1(u1_struct_0('#skF_5'), B_170, k2_pre_topc('#skF_5', k1_tarski(A_135)))=k1_tarski(A_135) | ~r1_tarski(k1_tarski(A_135), B_170) | ~v2_tex_2(B_170, '#skF_5') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden(A_135, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_975])).
% 3.93/1.70  tff(c_1501, plain, (![B_205, A_206]: (k9_subset_1(u1_struct_0('#skF_5'), B_205, k2_pre_topc('#skF_5', k1_tarski(A_206)))=k1_tarski(A_206) | ~r1_tarski(k1_tarski(A_206), B_205) | ~v2_tex_2(B_205, '#skF_5') | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(A_206, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_996])).
% 3.93/1.70  tff(c_73, plain, (![B_46, A_47]: (~r2_hidden(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.70  tff(c_77, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_73])).
% 3.93/1.70  tff(c_138, plain, (![B_68, A_69]: (v1_xboole_0(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.93/1.70  tff(c_147, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_138])).
% 3.93/1.70  tff(c_152, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_77, c_147])).
% 3.93/1.70  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_153, plain, (![A_70, B_71]: (k6_domain_1(A_70, B_71)=k1_tarski(B_71) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.93/1.70  tff(c_175, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_153])).
% 3.93/1.70  tff(c_196, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_152, c_175])).
% 3.93/1.70  tff(c_48, plain, (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.93/1.70  tff(c_197, plain, (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_5', k1_tarski('#skF_7')))!=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_48])).
% 3.93/1.70  tff(c_1507, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6') | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1501, c_197])).
% 3.93/1.70  tff(c_1514, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_1507])).
% 3.93/1.70  tff(c_1518, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_136, c_1514])).
% 3.93/1.70  tff(c_1522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1518])).
% 3.93/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.70  
% 3.93/1.70  Inference rules
% 3.93/1.70  ----------------------
% 3.93/1.70  #Ref     : 0
% 3.93/1.70  #Sup     : 351
% 3.93/1.70  #Fact    : 0
% 3.93/1.70  #Define  : 0
% 3.93/1.70  #Split   : 2
% 3.93/1.70  #Chain   : 0
% 3.93/1.70  #Close   : 0
% 3.93/1.70  
% 3.93/1.70  Ordering : KBO
% 3.93/1.70  
% 3.93/1.70  Simplification rules
% 3.93/1.70  ----------------------
% 3.93/1.70  #Subsume      : 45
% 3.93/1.70  #Demod        : 27
% 3.93/1.70  #Tautology    : 40
% 3.93/1.70  #SimpNegUnit  : 38
% 3.93/1.70  #BackRed      : 1
% 3.93/1.70  
% 3.93/1.70  #Partial instantiations: 0
% 3.93/1.70  #Strategies tried      : 1
% 3.93/1.70  
% 3.93/1.70  Timing (in seconds)
% 3.93/1.70  ----------------------
% 3.93/1.70  Preprocessing        : 0.33
% 3.93/1.70  Parsing              : 0.17
% 3.93/1.70  CNF conversion       : 0.03
% 3.93/1.70  Main loop            : 0.54
% 3.93/1.70  Inferencing          : 0.18
% 3.93/1.70  Reduction            : 0.15
% 3.93/1.70  Demodulation         : 0.09
% 3.93/1.70  BG Simplification    : 0.03
% 3.93/1.70  Subsumption          : 0.14
% 3.93/1.70  Abstraction          : 0.03
% 3.93/1.70  MUC search           : 0.00
% 3.93/1.70  Cooper               : 0.00
% 3.93/1.70  Total                : 0.91
% 3.93/1.70  Index Insertion      : 0.00
% 3.93/1.71  Index Deletion       : 0.00
% 3.93/1.71  Index Matching       : 0.00
% 3.93/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
