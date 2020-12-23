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
% DateTime   : Thu Dec  3 10:29:16 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   62 (  96 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 300 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_86,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_86])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_212,plain,(
    ! [A_98,B_99,C_100] :
      ( v3_pre_topc('#skF_1'(A_98,B_99,C_100),A_98)
      | ~ r1_tarski(C_100,B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_248,plain,(
    ! [A_107,B_108,A_109] :
      ( v3_pre_topc('#skF_1'(A_107,B_108,A_109),A_107)
      | ~ r1_tarski(A_109,B_108)
      | ~ v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ r1_tarski(A_109,u1_struct_0(A_107)) ) ),
    inference(resolution,[status(thm)],[c_14,c_212])).

tff(c_255,plain,(
    ! [A_109] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_109),'#skF_3')
      | ~ r1_tarski(A_109,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_109,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_248])).

tff(c_260,plain,(
    ! [A_109] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_109),'#skF_3')
      | ~ r1_tarski(A_109,'#skF_4')
      | ~ r1_tarski(A_109,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_255])).

tff(c_322,plain,(
    ! [A_128,B_129,C_130] :
      ( k9_subset_1(u1_struct_0(A_128),B_129,'#skF_1'(A_128,B_129,C_130)) = C_130
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_378,plain,(
    ! [A_133,B_134,A_135] :
      ( k9_subset_1(u1_struct_0(A_133),B_134,'#skF_1'(A_133,B_134,A_135)) = A_135
      | ~ r1_tarski(A_135,B_134)
      | ~ v2_tex_2(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ r1_tarski(A_135,u1_struct_0(A_133)) ) ),
    inference(resolution,[status(thm)],[c_14,c_322])).

tff(c_387,plain,(
    ! [A_135] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_135)) = A_135
      | ~ r1_tarski(A_135,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_135,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_378])).

tff(c_394,plain,(
    ! [A_136] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_136)) = A_136
      | ~ r1_tarski(A_136,'#skF_4')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_387])).

tff(c_262,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1('#skF_1'(A_111,B_112,C_113),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ r1_tarski(C_113,B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [D_49] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_49) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_49,'#skF_3')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_287,plain,(
    ! [B_112,C_113] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_112,C_113)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_112,C_113),'#skF_3')
      | ~ r1_tarski(C_113,B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_112,'#skF_3')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_262,c_30])).

tff(c_302,plain,(
    ! [B_112,C_113] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_112,C_113)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_112,C_113),'#skF_3')
      | ~ r1_tarski(C_113,B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_112,'#skF_3')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_287])).

tff(c_405,plain,(
    ! [A_136] :
      ( k1_tarski('#skF_5') != A_136
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_136),'#skF_3')
      | ~ r1_tarski(A_136,'#skF_4')
      | ~ m1_subset_1(A_136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_136,'#skF_4')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_302])).

tff(c_424,plain,(
    ! [A_137] :
      ( k1_tarski('#skF_5') != A_137
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_137),'#skF_3')
      | ~ m1_subset_1(A_137,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_137,'#skF_4')
      | ~ r1_tarski(A_137,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_405])).

tff(c_451,plain,(
    ! [A_138] :
      ( k1_tarski('#skF_5') != A_138
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_138),'#skF_3')
      | ~ r1_tarski(A_138,'#skF_4')
      | ~ r1_tarski(A_138,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_424])).

tff(c_471,plain,(
    ! [A_139] :
      ( k1_tarski('#skF_5') != A_139
      | ~ r1_tarski(A_139,'#skF_4')
      | ~ r1_tarski(A_139,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_260,c_451])).

tff(c_500,plain,(
    ! [A_140] :
      ( k1_tarski(A_140) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_140),'#skF_4')
      | ~ r2_hidden(A_140,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_471])).

tff(c_504,plain,(
    ! [A_6] :
      ( k1_tarski(A_6) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_6),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_6,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_500])).

tff(c_508,plain,(
    ! [A_141] :
      ( k1_tarski(A_141) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_141),'#skF_4')
      | ~ m1_subset_1(A_141,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_504])).

tff(c_514,plain,(
    ! [A_142] :
      ( k1_tarski(A_142) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_142,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_142,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_508])).

tff(c_517,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_514])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_517])).

tff(c_522,plain,(
    ! [A_66] : ~ r2_hidden(A_66,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  
% 2.80/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.80/1.42  
% 2.80/1.42  %Foreground sorts:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Background operators:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Foreground operators:
% 2.80/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.80/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.80/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.80/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.42  
% 2.80/1.43  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 2.80/1.43  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.80/1.43  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.80/1.43  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.80/1.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.43  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.80/1.43  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.43  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_86, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.43  tff(c_92, plain, (![A_66]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_86])).
% 2.80/1.43  tff(c_103, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.80/1.43  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.43  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.43  tff(c_212, plain, (![A_98, B_99, C_100]: (v3_pre_topc('#skF_1'(A_98, B_99, C_100), A_98) | ~r1_tarski(C_100, B_99) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_98))) | ~v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.43  tff(c_248, plain, (![A_107, B_108, A_109]: (v3_pre_topc('#skF_1'(A_107, B_108, A_109), A_107) | ~r1_tarski(A_109, B_108) | ~v2_tex_2(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~r1_tarski(A_109, u1_struct_0(A_107)))), inference(resolution, [status(thm)], [c_14, c_212])).
% 2.80/1.43  tff(c_255, plain, (![A_109]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_109), '#skF_3') | ~r1_tarski(A_109, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_109, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_248])).
% 2.80/1.43  tff(c_260, plain, (![A_109]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_109), '#skF_3') | ~r1_tarski(A_109, '#skF_4') | ~r1_tarski(A_109, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_255])).
% 2.80/1.43  tff(c_322, plain, (![A_128, B_129, C_130]: (k9_subset_1(u1_struct_0(A_128), B_129, '#skF_1'(A_128, B_129, C_130))=C_130 | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.43  tff(c_378, plain, (![A_133, B_134, A_135]: (k9_subset_1(u1_struct_0(A_133), B_134, '#skF_1'(A_133, B_134, A_135))=A_135 | ~r1_tarski(A_135, B_134) | ~v2_tex_2(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~r1_tarski(A_135, u1_struct_0(A_133)))), inference(resolution, [status(thm)], [c_14, c_322])).
% 2.80/1.43  tff(c_387, plain, (![A_135]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_135))=A_135 | ~r1_tarski(A_135, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_135, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_378])).
% 2.80/1.43  tff(c_394, plain, (![A_136]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_136))=A_136 | ~r1_tarski(A_136, '#skF_4') | ~r1_tarski(A_136, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_387])).
% 2.80/1.43  tff(c_262, plain, (![A_111, B_112, C_113]: (m1_subset_1('#skF_1'(A_111, B_112, C_113), k1_zfmisc_1(u1_struct_0(A_111))) | ~r1_tarski(C_113, B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_111))) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.43  tff(c_30, plain, (![D_49]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_49)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_49, '#skF_3') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.43  tff(c_287, plain, (![B_112, C_113]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_112, C_113))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_112, C_113), '#skF_3') | ~r1_tarski(C_113, B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_112, '#skF_3') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_262, c_30])).
% 2.80/1.43  tff(c_302, plain, (![B_112, C_113]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_112, C_113))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_112, C_113), '#skF_3') | ~r1_tarski(C_113, B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_112, '#skF_3') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_287])).
% 2.80/1.43  tff(c_405, plain, (![A_136]: (k1_tarski('#skF_5')!=A_136 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_136), '#skF_3') | ~r1_tarski(A_136, '#skF_4') | ~m1_subset_1(A_136, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_136, '#skF_4') | ~r1_tarski(A_136, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_394, c_302])).
% 2.80/1.43  tff(c_424, plain, (![A_137]: (k1_tarski('#skF_5')!=A_137 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_137), '#skF_3') | ~m1_subset_1(A_137, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_137, '#skF_4') | ~r1_tarski(A_137, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_405])).
% 2.80/1.43  tff(c_451, plain, (![A_138]: (k1_tarski('#skF_5')!=A_138 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_138), '#skF_3') | ~r1_tarski(A_138, '#skF_4') | ~r1_tarski(A_138, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_424])).
% 2.80/1.43  tff(c_471, plain, (![A_139]: (k1_tarski('#skF_5')!=A_139 | ~r1_tarski(A_139, '#skF_4') | ~r1_tarski(A_139, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_260, c_451])).
% 2.80/1.43  tff(c_500, plain, (![A_140]: (k1_tarski(A_140)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_140), '#skF_4') | ~r2_hidden(A_140, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_471])).
% 2.80/1.43  tff(c_504, plain, (![A_6]: (k1_tarski(A_6)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_6), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_6, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_500])).
% 2.80/1.43  tff(c_508, plain, (![A_141]: (k1_tarski(A_141)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_141), '#skF_4') | ~m1_subset_1(A_141, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_103, c_504])).
% 2.80/1.43  tff(c_514, plain, (![A_142]: (k1_tarski(A_142)!=k1_tarski('#skF_5') | ~m1_subset_1(A_142, u1_struct_0('#skF_3')) | ~r2_hidden(A_142, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_508])).
% 2.80/1.43  tff(c_517, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_514])).
% 2.80/1.43  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_517])).
% 2.80/1.43  tff(c_522, plain, (![A_66]: (~r2_hidden(A_66, '#skF_4'))), inference(splitRight, [status(thm)], [c_92])).
% 2.80/1.43  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_522, c_32])).
% 2.80/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  Inference rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Ref     : 0
% 2.80/1.43  #Sup     : 93
% 2.80/1.43  #Fact    : 0
% 2.80/1.43  #Define  : 0
% 2.80/1.43  #Split   : 3
% 2.80/1.43  #Chain   : 0
% 2.80/1.43  #Close   : 0
% 2.80/1.43  
% 2.80/1.43  Ordering : KBO
% 2.80/1.43  
% 2.80/1.43  Simplification rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Subsume      : 16
% 2.80/1.43  #Demod        : 51
% 2.80/1.43  #Tautology    : 14
% 2.80/1.43  #SimpNegUnit  : 2
% 2.80/1.43  #BackRed      : 1
% 2.80/1.43  
% 2.80/1.43  #Partial instantiations: 0
% 2.80/1.43  #Strategies tried      : 1
% 2.80/1.43  
% 2.80/1.43  Timing (in seconds)
% 2.80/1.43  ----------------------
% 2.80/1.44  Preprocessing        : 0.32
% 2.80/1.44  Parsing              : 0.16
% 2.80/1.44  CNF conversion       : 0.03
% 2.80/1.44  Main loop            : 0.36
% 2.80/1.44  Inferencing          : 0.14
% 2.80/1.44  Reduction            : 0.09
% 2.80/1.44  Demodulation         : 0.07
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.08
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.71
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
