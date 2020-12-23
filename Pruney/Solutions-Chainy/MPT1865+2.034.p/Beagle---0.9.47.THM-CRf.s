%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:22 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   60 (  92 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 293 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_tarski(A_66,B_67),C_68)
      | ~ r2_hidden(B_67,C_68)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_1,C_68] :
      ( r1_tarski(k1_tarski(A_1),C_68)
      | ~ r2_hidden(A_1,C_68)
      | ~ r2_hidden(A_1,C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_75,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_69])).

tff(c_76,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [A_92,B_93,C_94] :
      ( v4_pre_topc('#skF_1'(A_92,B_93,C_94),A_92)
      | ~ r1_tarski(C_94,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_180,plain,(
    ! [A_92,B_93,A_5] :
      ( v4_pre_topc('#skF_1'(A_92,B_93,k1_tarski(A_5)),A_92)
      | ~ r1_tarski(k1_tarski(A_5),B_93)
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ r2_hidden(A_5,u1_struct_0(A_92)) ) ),
    inference(resolution,[status(thm)],[c_10,c_171])).

tff(c_244,plain,(
    ! [A_112,B_113,C_114] :
      ( k9_subset_1(u1_struct_0(A_112),B_113,'#skF_1'(A_112,B_113,C_114)) = C_114
      | ~ r1_tarski(C_114,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_256,plain,(
    ! [A_112,B_113,A_5] :
      ( k9_subset_1(u1_struct_0(A_112),B_113,'#skF_1'(A_112,B_113,k1_tarski(A_5))) = k1_tarski(A_5)
      | ~ r1_tarski(k1_tarski(A_5),B_113)
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ r2_hidden(A_5,u1_struct_0(A_112)) ) ),
    inference(resolution,[status(thm)],[c_10,c_244])).

tff(c_210,plain,(
    ! [A_109,B_110,C_111] :
      ( m1_subset_1('#skF_1'(A_109,B_110,C_111),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ r1_tarski(C_111,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [D_48] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_48) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_48,'#skF_3')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    ! [B_110,C_111] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_110,C_111)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_110,C_111),'#skF_3')
      | ~ r1_tarski(C_111,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_110,'#skF_3')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_210,c_28])).

tff(c_313,plain,(
    ! [B_128,C_129] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_128,C_129)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_128,C_129),'#skF_3')
      | ~ r1_tarski(C_129,B_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_230])).

tff(c_316,plain,(
    ! [A_5] :
      ( k1_tarski(A_5) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_5)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_5),'#skF_4')
      | ~ m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_5),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_5,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_313])).

tff(c_319,plain,(
    ! [A_130] :
      ( k1_tarski(A_130) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_130)),'#skF_3')
      | ~ m1_subset_1(k1_tarski(A_130),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_130),'#skF_4')
      | ~ r2_hidden(A_130,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_36,c_34,c_316])).

tff(c_325,plain,(
    ! [A_131] :
      ( k1_tarski(A_131) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_131)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_131),'#skF_4')
      | ~ r2_hidden(A_131,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_319])).

tff(c_329,plain,(
    ! [A_5] :
      ( k1_tarski(A_5) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_5),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_5,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_180,c_325])).

tff(c_333,plain,(
    ! [A_132] :
      ( k1_tarski(A_132) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_132),'#skF_4')
      | ~ r2_hidden(A_132,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_329])).

tff(c_337,plain,(
    ! [A_7] :
      ( k1_tarski(A_7) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_7),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_7,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_333])).

tff(c_341,plain,(
    ! [A_133] :
      ( k1_tarski(A_133) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_133),'#skF_4')
      | ~ m1_subset_1(A_133,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_337])).

tff(c_347,plain,(
    ! [A_134] :
      ( k1_tarski(A_134) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_134,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_134,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_341])).

tff(c_350,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_347])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_350])).

tff(c_355,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.59/1.41  
% 2.59/1.41  %Foreground sorts:
% 2.59/1.41  
% 2.59/1.41  
% 2.59/1.41  %Background operators:
% 2.59/1.41  
% 2.59/1.41  
% 2.59/1.41  %Foreground operators:
% 2.59/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.59/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.59/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.41  
% 2.59/1.43  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 2.59/1.43  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.59/1.43  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.59/1.43  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.59/1.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.59/1.43  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.59/1.43  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.59/1.43  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.59/1.43  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.59/1.43  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.43  tff(c_77, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_tarski(A_66, B_67), C_68) | ~r2_hidden(B_67, C_68) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.43  tff(c_86, plain, (![A_1, C_68]: (r1_tarski(k1_tarski(A_1), C_68) | ~r2_hidden(A_1, C_68) | ~r2_hidden(A_1, C_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 2.59/1.43  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.59/1.43  tff(c_69, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.43  tff(c_75, plain, (![A_65]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_69])).
% 2.59/1.43  tff(c_76, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_75])).
% 2.59/1.43  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.43  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.59/1.43  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.59/1.43  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.43  tff(c_171, plain, (![A_92, B_93, C_94]: (v4_pre_topc('#skF_1'(A_92, B_93, C_94), A_92) | ~r1_tarski(C_94, B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.43  tff(c_180, plain, (![A_92, B_93, A_5]: (v4_pre_topc('#skF_1'(A_92, B_93, k1_tarski(A_5)), A_92) | ~r1_tarski(k1_tarski(A_5), B_93) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~r2_hidden(A_5, u1_struct_0(A_92)))), inference(resolution, [status(thm)], [c_10, c_171])).
% 2.59/1.43  tff(c_244, plain, (![A_112, B_113, C_114]: (k9_subset_1(u1_struct_0(A_112), B_113, '#skF_1'(A_112, B_113, C_114))=C_114 | ~r1_tarski(C_114, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.43  tff(c_256, plain, (![A_112, B_113, A_5]: (k9_subset_1(u1_struct_0(A_112), B_113, '#skF_1'(A_112, B_113, k1_tarski(A_5)))=k1_tarski(A_5) | ~r1_tarski(k1_tarski(A_5), B_113) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~r2_hidden(A_5, u1_struct_0(A_112)))), inference(resolution, [status(thm)], [c_10, c_244])).
% 2.59/1.43  tff(c_210, plain, (![A_109, B_110, C_111]: (m1_subset_1('#skF_1'(A_109, B_110, C_111), k1_zfmisc_1(u1_struct_0(A_109))) | ~r1_tarski(C_111, B_110) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_109))) | ~v2_tex_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.43  tff(c_28, plain, (![D_48]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_48)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_48, '#skF_3') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.59/1.43  tff(c_230, plain, (![B_110, C_111]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_110, C_111))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_110, C_111), '#skF_3') | ~r1_tarski(C_111, B_110) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_110, '#skF_3') | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_210, c_28])).
% 2.59/1.43  tff(c_313, plain, (![B_128, C_129]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_128, C_129))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_128, C_129), '#skF_3') | ~r1_tarski(C_129, B_128) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_230])).
% 2.59/1.43  tff(c_316, plain, (![A_5]: (k1_tarski(A_5)!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_5)), '#skF_3') | ~r1_tarski(k1_tarski(A_5), '#skF_4') | ~m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_5), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_5, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_256, c_313])).
% 2.59/1.43  tff(c_319, plain, (![A_130]: (k1_tarski(A_130)!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_130)), '#skF_3') | ~m1_subset_1(k1_tarski(A_130), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_130), '#skF_4') | ~r2_hidden(A_130, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_36, c_34, c_316])).
% 2.59/1.43  tff(c_325, plain, (![A_131]: (k1_tarski(A_131)!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_131)), '#skF_3') | ~r1_tarski(k1_tarski(A_131), '#skF_4') | ~r2_hidden(A_131, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_319])).
% 2.59/1.43  tff(c_329, plain, (![A_5]: (k1_tarski(A_5)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_5), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_5, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_180, c_325])).
% 2.59/1.43  tff(c_333, plain, (![A_132]: (k1_tarski(A_132)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_132), '#skF_4') | ~r2_hidden(A_132, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_329])).
% 2.59/1.43  tff(c_337, plain, (![A_7]: (k1_tarski(A_7)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_7), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_7, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_333])).
% 2.59/1.43  tff(c_341, plain, (![A_133]: (k1_tarski(A_133)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_133), '#skF_4') | ~m1_subset_1(A_133, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_76, c_337])).
% 2.59/1.43  tff(c_347, plain, (![A_134]: (k1_tarski(A_134)!=k1_tarski('#skF_5') | ~m1_subset_1(A_134, u1_struct_0('#skF_3')) | ~r2_hidden(A_134, '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_341])).
% 2.59/1.43  tff(c_350, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_347])).
% 2.59/1.43  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_350])).
% 2.59/1.43  tff(c_355, plain, (![A_65]: (~r2_hidden(A_65, '#skF_4'))), inference(splitRight, [status(thm)], [c_75])).
% 2.59/1.43  tff(c_370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_355, c_30])).
% 2.59/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.43  
% 2.59/1.43  Inference rules
% 2.59/1.43  ----------------------
% 2.59/1.43  #Ref     : 0
% 2.59/1.43  #Sup     : 64
% 2.59/1.43  #Fact    : 0
% 2.59/1.43  #Define  : 0
% 2.59/1.43  #Split   : 4
% 2.59/1.43  #Chain   : 0
% 2.59/1.43  #Close   : 0
% 2.59/1.43  
% 2.59/1.43  Ordering : KBO
% 2.59/1.43  
% 2.59/1.43  Simplification rules
% 2.59/1.43  ----------------------
% 2.59/1.43  #Subsume      : 5
% 2.59/1.43  #Demod        : 27
% 2.59/1.43  #Tautology    : 16
% 2.59/1.43  #SimpNegUnit  : 2
% 2.59/1.43  #BackRed      : 1
% 2.59/1.43  
% 2.59/1.43  #Partial instantiations: 0
% 2.59/1.43  #Strategies tried      : 1
% 2.59/1.43  
% 2.59/1.43  Timing (in seconds)
% 2.59/1.43  ----------------------
% 2.59/1.43  Preprocessing        : 0.33
% 2.59/1.43  Parsing              : 0.18
% 2.59/1.43  CNF conversion       : 0.03
% 2.59/1.43  Main loop            : 0.28
% 2.59/1.43  Inferencing          : 0.12
% 2.59/1.43  Reduction            : 0.07
% 2.59/1.43  Demodulation         : 0.05
% 2.59/1.43  BG Simplification    : 0.02
% 2.59/1.43  Subsumption          : 0.05
% 2.59/1.43  Abstraction          : 0.02
% 2.59/1.43  MUC search           : 0.00
% 2.59/1.43  Cooper               : 0.00
% 2.59/1.43  Total                : 0.64
% 2.59/1.43  Index Insertion      : 0.00
% 2.59/1.43  Index Deletion       : 0.00
% 2.59/1.43  Index Matching       : 0.00
% 2.59/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
