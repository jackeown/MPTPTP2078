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
% DateTime   : Thu Dec  3 10:23:04 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 200 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 ( 564 expanded)
%              Number of equality atoms :    4 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v2_tops_2(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                     => ( D = B
                       => v2_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_36,plain,(
    ~ v2_tops_2('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    ! [B_54,A_55] :
      ( l1_pre_topc(B_54)
      | ~ m1_pre_topc(B_54,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_70,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_55,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    r1_tarski('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_88,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_38,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_63,plain,(
    r1_tarski('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_50,c_55])).

tff(c_266,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_4'(A_104,B_105),B_105)
      | v2_tops_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_104))))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_271,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | v2_tops_2('#skF_8','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_266])).

tff(c_277,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | v2_tops_2('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_271])).

tff(c_278,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_277])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_8'),B_106)
      | ~ r1_tarski('#skF_8',B_106) ) ),
    inference(resolution,[status(thm)],[c_278,c_2])).

tff(c_302,plain,(
    ! [B_108,B_109] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_8'),B_108)
      | ~ r1_tarski(B_109,B_108)
      | ~ r1_tarski('#skF_8',B_109) ) ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_318,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_63,c_302])).

tff(c_330,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_318])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_340,plain,(
    r1_tarski('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_330,c_8])).

tff(c_42,plain,(
    v2_tops_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_49,plain,(
    v2_tops_2('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_671,plain,(
    ! [C_140,A_141,B_142] :
      ( v4_pre_topc(C_140,A_141)
      | ~ r2_hidden(C_140,B_142)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v2_tops_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_141))))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_732,plain,(
    ! [A_145] :
      ( v4_pre_topc('#skF_4'('#skF_7','#skF_8'),A_145)
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v2_tops_2('#skF_8',A_145)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_278,c_671])).

tff(c_910,plain,(
    ! [A_153] :
      ( v4_pre_topc('#skF_4'('#skF_7','#skF_8'),A_153)
      | ~ v2_tops_2('#skF_8',A_153)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153))))
      | ~ l1_pre_topc(A_153)
      | ~ r1_tarski('#skF_4'('#skF_7','#skF_8'),u1_struct_0(A_153)) ) ),
    inference(resolution,[status(thm)],[c_22,c_732])).

tff(c_919,plain,
    ( v4_pre_topc('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ v2_tops_2('#skF_8','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_910])).

tff(c_926,plain,(
    v4_pre_topc('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_48,c_49,c_919])).

tff(c_293,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_4'('#skF_7','#skF_8'),A_6)
      | ~ r1_tarski('#skF_8',k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_285,c_8])).

tff(c_567,plain,(
    ! [D_132,C_133,A_134] :
      ( v4_pre_topc(D_132,C_133)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(C_133)))
      | ~ v4_pre_topc(D_132,A_134)
      | ~ m1_pre_topc(C_133,A_134)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1980,plain,(
    ! [A_210,C_211,A_212] :
      ( v4_pre_topc(A_210,C_211)
      | ~ v4_pre_topc(A_210,A_212)
      | ~ m1_pre_topc(C_211,A_212)
      | ~ m1_subset_1(A_210,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ r1_tarski(A_210,u1_struct_0(C_211)) ) ),
    inference(resolution,[status(thm)],[c_22,c_567])).

tff(c_1982,plain,(
    ! [A_210] :
      ( v4_pre_topc(A_210,'#skF_7')
      | ~ v4_pre_topc(A_210,'#skF_5')
      | ~ m1_subset_1(A_210,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_210,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1980])).

tff(c_2067,plain,(
    ! [A_216] :
      ( v4_pre_topc(A_216,'#skF_7')
      | ~ v4_pre_topc(A_216,'#skF_5')
      | ~ m1_subset_1(A_216,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_216,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1982])).

tff(c_2295,plain,(
    ! [A_225] :
      ( v4_pre_topc(A_225,'#skF_7')
      | ~ v4_pre_topc(A_225,'#skF_5')
      | ~ r1_tarski(A_225,u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_225,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_22,c_2067])).

tff(c_2325,plain,
    ( v4_pre_topc('#skF_4'('#skF_7','#skF_8'),'#skF_7')
    | ~ v4_pre_topc('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_5'))
    | ~ r1_tarski('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_293,c_2295])).

tff(c_2358,plain,(
    v4_pre_topc('#skF_4'('#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_340,c_926,c_2325])).

tff(c_28,plain,(
    ! [A_16,B_22] :
      ( ~ v4_pre_topc('#skF_4'(A_16,B_22),A_16)
      | v2_tops_2(B_22,A_16)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2365,plain,
    ( v2_tops_2('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_2358,c_28])).

tff(c_2368,plain,(
    v2_tops_2('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40,c_2365])).

tff(c_2370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.89  
% 4.53/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.89  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.53/1.89  
% 4.53/1.89  %Foreground sorts:
% 4.53/1.89  
% 4.53/1.89  
% 4.53/1.89  %Background operators:
% 4.53/1.89  
% 4.53/1.89  
% 4.53/1.89  %Foreground operators:
% 4.53/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.53/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.53/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.53/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.89  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 4.53/1.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.53/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.53/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.53/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.53/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.53/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.53/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.89  
% 4.53/1.90  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v2_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v2_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tops_2)).
% 4.53/1.90  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.53/1.90  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.53/1.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.53/1.90  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 4.53/1.90  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.53/1.90  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 4.53/1.90  tff(c_36, plain, (~v2_tops_2('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_44, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_64, plain, (![B_54, A_55]: (l1_pre_topc(B_54) | ~m1_pre_topc(B_54, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.53/1.90  tff(c_67, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_44, c_64])).
% 4.53/1.90  tff(c_70, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67])).
% 4.53/1.90  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_55, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.53/1.90  tff(c_62, plain, (r1_tarski('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_40, c_55])).
% 4.53/1.90  tff(c_88, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.90  tff(c_97, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_88, c_4])).
% 4.53/1.90  tff(c_38, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 4.53/1.90  tff(c_63, plain, (r1_tarski('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_55])).
% 4.53/1.90  tff(c_266, plain, (![A_104, B_105]: (r2_hidden('#skF_4'(A_104, B_105), B_105) | v2_tops_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_104)))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.53/1.90  tff(c_271, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_8') | v2_tops_2('#skF_8', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_266])).
% 4.53/1.90  tff(c_277, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_8') | v2_tops_2('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_271])).
% 4.53/1.90  tff(c_278, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_36, c_277])).
% 4.53/1.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.90  tff(c_285, plain, (![B_106]: (r2_hidden('#skF_4'('#skF_7', '#skF_8'), B_106) | ~r1_tarski('#skF_8', B_106))), inference(resolution, [status(thm)], [c_278, c_2])).
% 4.53/1.90  tff(c_302, plain, (![B_108, B_109]: (r2_hidden('#skF_4'('#skF_7', '#skF_8'), B_108) | ~r1_tarski(B_109, B_108) | ~r1_tarski('#skF_8', B_109))), inference(resolution, [status(thm)], [c_285, c_2])).
% 4.53/1.90  tff(c_318, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_63, c_302])).
% 4.53/1.90  tff(c_330, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_318])).
% 4.53/1.90  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.53/1.90  tff(c_340, plain, (r1_tarski('#skF_4'('#skF_7', '#skF_8'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_330, c_8])).
% 4.53/1.90  tff(c_42, plain, (v2_tops_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.53/1.90  tff(c_49, plain, (v2_tops_2('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 4.53/1.90  tff(c_22, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.53/1.90  tff(c_671, plain, (![C_140, A_141, B_142]: (v4_pre_topc(C_140, A_141) | ~r2_hidden(C_140, B_142) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~v2_tops_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_141)))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.53/1.90  tff(c_732, plain, (![A_145]: (v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), A_145) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0(A_145))) | ~v2_tops_2('#skF_8', A_145) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_278, c_671])).
% 4.53/1.90  tff(c_910, plain, (![A_153]: (v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), A_153) | ~v2_tops_2('#skF_8', A_153) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153)))) | ~l1_pre_topc(A_153) | ~r1_tarski('#skF_4'('#skF_7', '#skF_8'), u1_struct_0(A_153)))), inference(resolution, [status(thm)], [c_22, c_732])).
% 4.53/1.90  tff(c_919, plain, (v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | ~v2_tops_2('#skF_8', '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski('#skF_4'('#skF_7', '#skF_8'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_910])).
% 4.53/1.90  tff(c_926, plain, (v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_48, c_49, c_919])).
% 4.53/1.90  tff(c_293, plain, (![A_6]: (r1_tarski('#skF_4'('#skF_7', '#skF_8'), A_6) | ~r1_tarski('#skF_8', k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_285, c_8])).
% 4.53/1.90  tff(c_567, plain, (![D_132, C_133, A_134]: (v4_pre_topc(D_132, C_133) | ~m1_subset_1(D_132, k1_zfmisc_1(u1_struct_0(C_133))) | ~v4_pre_topc(D_132, A_134) | ~m1_pre_topc(C_133, A_134) | ~m1_subset_1(D_132, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.53/1.90  tff(c_1980, plain, (![A_210, C_211, A_212]: (v4_pre_topc(A_210, C_211) | ~v4_pre_topc(A_210, A_212) | ~m1_pre_topc(C_211, A_212) | ~m1_subset_1(A_210, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212) | ~r1_tarski(A_210, u1_struct_0(C_211)))), inference(resolution, [status(thm)], [c_22, c_567])).
% 4.53/1.90  tff(c_1982, plain, (![A_210]: (v4_pre_topc(A_210, '#skF_7') | ~v4_pre_topc(A_210, '#skF_5') | ~m1_subset_1(A_210, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_210, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_44, c_1980])).
% 4.53/1.90  tff(c_2067, plain, (![A_216]: (v4_pre_topc(A_216, '#skF_7') | ~v4_pre_topc(A_216, '#skF_5') | ~m1_subset_1(A_216, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_216, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1982])).
% 4.53/1.90  tff(c_2295, plain, (![A_225]: (v4_pre_topc(A_225, '#skF_7') | ~v4_pre_topc(A_225, '#skF_5') | ~r1_tarski(A_225, u1_struct_0('#skF_7')) | ~r1_tarski(A_225, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_22, c_2067])).
% 4.53/1.90  tff(c_2325, plain, (v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), '#skF_7') | ~v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | ~r1_tarski('#skF_4'('#skF_7', '#skF_8'), u1_struct_0('#skF_5')) | ~r1_tarski('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_293, c_2295])).
% 4.53/1.90  tff(c_2358, plain, (v4_pre_topc('#skF_4'('#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_340, c_926, c_2325])).
% 4.53/1.90  tff(c_28, plain, (![A_16, B_22]: (~v4_pre_topc('#skF_4'(A_16, B_22), A_16) | v2_tops_2(B_22, A_16) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.53/1.90  tff(c_2365, plain, (v2_tops_2('#skF_8', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7')))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_2358, c_28])).
% 4.53/1.90  tff(c_2368, plain, (v2_tops_2('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40, c_2365])).
% 4.53/1.90  tff(c_2370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_2368])).
% 4.53/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.90  
% 4.53/1.90  Inference rules
% 4.53/1.90  ----------------------
% 4.53/1.90  #Ref     : 0
% 4.53/1.90  #Sup     : 571
% 4.53/1.90  #Fact    : 0
% 4.53/1.90  #Define  : 0
% 4.53/1.90  #Split   : 17
% 4.53/1.90  #Chain   : 0
% 4.53/1.90  #Close   : 0
% 4.53/1.90  
% 4.53/1.90  Ordering : KBO
% 4.53/1.90  
% 4.53/1.90  Simplification rules
% 4.53/1.90  ----------------------
% 4.53/1.90  #Subsume      : 148
% 4.53/1.90  #Demod        : 67
% 4.53/1.90  #Tautology    : 37
% 4.53/1.90  #SimpNegUnit  : 7
% 4.53/1.90  #BackRed      : 0
% 4.53/1.90  
% 4.53/1.91  #Partial instantiations: 0
% 4.53/1.91  #Strategies tried      : 1
% 4.53/1.91  
% 4.53/1.91  Timing (in seconds)
% 4.53/1.91  ----------------------
% 4.96/1.91  Preprocessing        : 0.30
% 4.96/1.91  Parsing              : 0.15
% 4.96/1.91  CNF conversion       : 0.03
% 4.96/1.91  Main loop            : 0.80
% 4.96/1.91  Inferencing          : 0.24
% 4.96/1.91  Reduction            : 0.23
% 4.96/1.91  Demodulation         : 0.15
% 4.96/1.91  BG Simplification    : 0.03
% 4.96/1.91  Subsumption          : 0.25
% 4.96/1.91  Abstraction          : 0.03
% 4.96/1.91  MUC search           : 0.00
% 4.96/1.91  Cooper               : 0.00
% 4.96/1.91  Total                : 1.13
% 4.96/1.91  Index Insertion      : 0.00
% 4.96/1.91  Index Deletion       : 0.00
% 4.96/1.91  Index Matching       : 0.00
% 4.96/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
