%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:16 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   58 (  90 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 286 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_75,plain,(
    ! [C_62,B_63,A_64] :
      ( ~ v1_xboole_0(C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_82,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [A_78,B_79,C_80] :
      ( v3_pre_topc('#skF_1'(A_78,B_79,C_80),A_78)
      | ~ r1_tarski(C_80,B_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,(
    ! [A_78,B_79,A_6] :
      ( v3_pre_topc('#skF_1'(A_78,B_79,k1_tarski(A_6)),A_78)
      | ~ r1_tarski(k1_tarski(A_6),B_79)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ r2_hidden(A_6,u1_struct_0(A_78)) ) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_234,plain,(
    ! [A_108,B_109,C_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,'#skF_1'(A_108,B_109,C_110)) = C_110
      | ~ r1_tarski(C_110,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_290,plain,(
    ! [A_117,B_118,A_119] :
      ( k9_subset_1(u1_struct_0(A_117),B_118,'#skF_1'(A_117,B_118,k1_tarski(A_119))) = k1_tarski(A_119)
      | ~ r1_tarski(k1_tarski(A_119),B_118)
      | ~ v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ r2_hidden(A_119,u1_struct_0(A_117)) ) ),
    inference(resolution,[status(thm)],[c_10,c_234])).

tff(c_195,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1('#skF_1'(A_93,B_94,C_95),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ r1_tarski(C_95,B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [D_49] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_49) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_49,'#skF_3')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_215,plain,(
    ! [B_94,C_95] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_94,C_95)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_94,C_95),'#skF_3')
      | ~ r1_tarski(C_95,B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_94,'#skF_3')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_195,c_28])).

tff(c_228,plain,(
    ! [B_94,C_95] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_94,C_95)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_94,C_95),'#skF_3')
      | ~ r1_tarski(C_95,B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_94,'#skF_3')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_215])).

tff(c_296,plain,(
    ! [A_119] :
      ( k1_tarski(A_119) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_119)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_119),'#skF_4')
      | ~ m1_subset_1(k1_tarski(A_119),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_119),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_119,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_228])).

tff(c_306,plain,(
    ! [A_120] :
      ( k1_tarski(A_120) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_120)),'#skF_3')
      | ~ m1_subset_1(k1_tarski(A_120),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_120),'#skF_4')
      | ~ r2_hidden(A_120,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_36,c_34,c_296])).

tff(c_312,plain,(
    ! [A_121] :
      ( k1_tarski(A_121) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_121)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_121),'#skF_4')
      | ~ r2_hidden(A_121,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_306])).

tff(c_316,plain,(
    ! [A_6] :
      ( k1_tarski(A_6) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_6),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_6,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_132,c_312])).

tff(c_320,plain,(
    ! [A_122] :
      ( k1_tarski(A_122) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_122),'#skF_4')
      | ~ r2_hidden(A_122,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_316])).

tff(c_324,plain,(
    ! [A_8] :
      ( k1_tarski(A_8) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_8),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_8,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_320])).

tff(c_328,plain,(
    ! [A_123] :
      ( k1_tarski(A_123) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_123),'#skF_4')
      | ~ m1_subset_1(A_123,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_324])).

tff(c_334,plain,(
    ! [A_124] :
      ( k1_tarski(A_124) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_124,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_328])).

tff(c_337,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_334])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_337])).

tff(c_342,plain,(
    ! [A_64] : ~ r2_hidden(A_64,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:59 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.38  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.54/1.38  
% 2.54/1.38  %Foreground sorts:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Background operators:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Foreground operators:
% 2.54/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.54/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.54/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.54/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.54/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.38  
% 2.81/1.40  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 2.81/1.40  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.81/1.40  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.81/1.40  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.40  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.81/1.40  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.81/1.40  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.40  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.40  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.40  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.40  tff(c_75, plain, (![C_62, B_63, A_64]: (~v1_xboole_0(C_62) | ~m1_subset_1(B_63, k1_zfmisc_1(C_62)) | ~r2_hidden(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.40  tff(c_81, plain, (![A_64]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_75])).
% 2.81/1.40  tff(c_82, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_81])).
% 2.81/1.40  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.40  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.40  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.40  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.40  tff(c_123, plain, (![A_78, B_79, C_80]: (v3_pre_topc('#skF_1'(A_78, B_79, C_80), A_78) | ~r1_tarski(C_80, B_79) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.40  tff(c_132, plain, (![A_78, B_79, A_6]: (v3_pre_topc('#skF_1'(A_78, B_79, k1_tarski(A_6)), A_78) | ~r1_tarski(k1_tarski(A_6), B_79) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~r2_hidden(A_6, u1_struct_0(A_78)))), inference(resolution, [status(thm)], [c_10, c_123])).
% 2.81/1.40  tff(c_234, plain, (![A_108, B_109, C_110]: (k9_subset_1(u1_struct_0(A_108), B_109, '#skF_1'(A_108, B_109, C_110))=C_110 | ~r1_tarski(C_110, B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.40  tff(c_290, plain, (![A_117, B_118, A_119]: (k9_subset_1(u1_struct_0(A_117), B_118, '#skF_1'(A_117, B_118, k1_tarski(A_119)))=k1_tarski(A_119) | ~r1_tarski(k1_tarski(A_119), B_118) | ~v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~r2_hidden(A_119, u1_struct_0(A_117)))), inference(resolution, [status(thm)], [c_10, c_234])).
% 2.81/1.40  tff(c_195, plain, (![A_93, B_94, C_95]: (m1_subset_1('#skF_1'(A_93, B_94, C_95), k1_zfmisc_1(u1_struct_0(A_93))) | ~r1_tarski(C_95, B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_93))) | ~v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.40  tff(c_28, plain, (![D_49]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_49)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_49, '#skF_3') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.40  tff(c_215, plain, (![B_94, C_95]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_94, C_95))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_94, C_95), '#skF_3') | ~r1_tarski(C_95, B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_94, '#skF_3') | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_195, c_28])).
% 2.81/1.40  tff(c_228, plain, (![B_94, C_95]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_94, C_95))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_94, C_95), '#skF_3') | ~r1_tarski(C_95, B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_94, '#skF_3') | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_215])).
% 2.81/1.40  tff(c_296, plain, (![A_119]: (k1_tarski(A_119)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_119)), '#skF_3') | ~r1_tarski(k1_tarski(A_119), '#skF_4') | ~m1_subset_1(k1_tarski(A_119), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_119), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_119, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_290, c_228])).
% 2.81/1.40  tff(c_306, plain, (![A_120]: (k1_tarski(A_120)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_120)), '#skF_3') | ~m1_subset_1(k1_tarski(A_120), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_120), '#skF_4') | ~r2_hidden(A_120, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_36, c_34, c_296])).
% 2.81/1.40  tff(c_312, plain, (![A_121]: (k1_tarski(A_121)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_121)), '#skF_3') | ~r1_tarski(k1_tarski(A_121), '#skF_4') | ~r2_hidden(A_121, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_306])).
% 2.81/1.40  tff(c_316, plain, (![A_6]: (k1_tarski(A_6)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_6), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_6, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_132, c_312])).
% 2.81/1.40  tff(c_320, plain, (![A_122]: (k1_tarski(A_122)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_122), '#skF_4') | ~r2_hidden(A_122, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_316])).
% 2.81/1.40  tff(c_324, plain, (![A_8]: (k1_tarski(A_8)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_8), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_8, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_320])).
% 2.81/1.40  tff(c_328, plain, (![A_123]: (k1_tarski(A_123)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_123), '#skF_4') | ~m1_subset_1(A_123, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_324])).
% 2.81/1.40  tff(c_334, plain, (![A_124]: (k1_tarski(A_124)!=k1_tarski('#skF_5') | ~m1_subset_1(A_124, u1_struct_0('#skF_3')) | ~r2_hidden(A_124, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_328])).
% 2.81/1.40  tff(c_337, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_334])).
% 2.81/1.40  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_337])).
% 2.81/1.40  tff(c_342, plain, (![A_64]: (~r2_hidden(A_64, '#skF_4'))), inference(splitRight, [status(thm)], [c_81])).
% 2.81/1.40  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_30])).
% 2.81/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  Inference rules
% 2.81/1.40  ----------------------
% 2.81/1.40  #Ref     : 0
% 2.81/1.40  #Sup     : 58
% 2.81/1.40  #Fact    : 0
% 2.81/1.40  #Define  : 0
% 2.81/1.40  #Split   : 4
% 2.81/1.40  #Chain   : 0
% 2.81/1.40  #Close   : 0
% 2.81/1.40  
% 2.81/1.40  Ordering : KBO
% 2.81/1.40  
% 2.81/1.40  Simplification rules
% 2.81/1.40  ----------------------
% 2.81/1.40  #Subsume      : 4
% 2.81/1.40  #Demod        : 27
% 2.81/1.40  #Tautology    : 14
% 2.81/1.40  #SimpNegUnit  : 2
% 2.81/1.40  #BackRed      : 1
% 2.81/1.40  
% 2.81/1.40  #Partial instantiations: 0
% 2.81/1.40  #Strategies tried      : 1
% 2.81/1.40  
% 2.81/1.40  Timing (in seconds)
% 2.81/1.40  ----------------------
% 2.81/1.40  Preprocessing        : 0.32
% 2.81/1.40  Parsing              : 0.17
% 2.81/1.40  CNF conversion       : 0.03
% 2.81/1.40  Main loop            : 0.30
% 2.81/1.40  Inferencing          : 0.12
% 2.81/1.40  Reduction            : 0.08
% 2.81/1.40  Demodulation         : 0.06
% 2.81/1.40  BG Simplification    : 0.02
% 2.81/1.40  Subsumption          : 0.06
% 2.81/1.40  Abstraction          : 0.02
% 2.81/1.40  MUC search           : 0.00
% 2.81/1.40  Cooper               : 0.00
% 2.81/1.40  Total                : 0.66
% 2.81/1.40  Index Insertion      : 0.00
% 2.81/1.40  Index Deletion       : 0.00
% 2.81/1.40  Index Matching       : 0.00
% 2.81/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
