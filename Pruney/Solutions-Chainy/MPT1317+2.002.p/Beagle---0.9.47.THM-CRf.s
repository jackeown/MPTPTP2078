%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:04 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 290 expanded)
%              Number of leaves         :   26 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 864 expanded)
%              Number of equality atoms :    4 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_34,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ~ v2_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    ~ v2_tops_2('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,(
    ! [B_55,A_56] :
      ( l1_pre_topc(B_55)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_59,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_45,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_60,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_45,c_60])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_123,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_3'(A_80,B_81),B_81)
      | v2_tops_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80))))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_45,c_123])).

tff(c_134,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_128])).

tff(c_135,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_134])).

tff(c_14,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_143,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5'),A_84)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_135,c_14])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_3'('#skF_6','#skF_5'),A_85)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_164,plain,(
    r1_tarski('#skF_3'('#skF_6','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_152])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_3'('#skF_6','#skF_5'),A_85)
      | ~ r1_tarski('#skF_5',k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_231,plain,(
    ! [D_97,C_98,A_99] :
      ( v4_pre_topc(D_97,C_98)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(u1_struct_0(C_98)))
      | ~ v4_pre_topc(D_97,A_99)
      | ~ m1_pre_topc(C_98,A_99)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_483,plain,(
    ! [A_133,C_134,A_135] :
      ( v4_pre_topc(A_133,C_134)
      | ~ v4_pre_topc(A_133,A_135)
      | ~ m1_pre_topc(C_134,A_135)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ r1_tarski(A_133,u1_struct_0(C_134)) ) ),
    inference(resolution,[status(thm)],[c_18,c_231])).

tff(c_485,plain,(
    ! [A_133] :
      ( v4_pre_topc(A_133,'#skF_6')
      | ~ v4_pre_topc(A_133,'#skF_4')
      | ~ m1_subset_1(A_133,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_133,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_40,c_483])).

tff(c_598,plain,(
    ! [A_142] :
      ( v4_pre_topc(A_142,'#skF_6')
      | ~ v4_pre_topc(A_142,'#skF_4')
      | ~ m1_subset_1(A_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_142,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_485])).

tff(c_622,plain,(
    ! [A_150] :
      ( v4_pre_topc(A_150,'#skF_6')
      | ~ v4_pre_topc(A_150,'#skF_4')
      | ~ r1_tarski(A_150,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_150,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_598])).

tff(c_656,plain,
    ( v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_6')
    | ~ v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_3'('#skF_6','#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_162,c_622])).

tff(c_675,plain,
    ( v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_6')
    | ~ v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_164,c_656])).

tff(c_680,plain,(
    ~ v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_675])).

tff(c_38,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_321,plain,(
    ! [C_111,A_112,B_113] :
      ( v4_pre_topc(C_111,A_112)
      | ~ r2_hidden(C_111,B_113)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v2_tops_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112))))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_366,plain,(
    ! [A_120] :
      ( v4_pre_topc('#skF_3'('#skF_6','#skF_5'),A_120)
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_5'),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v2_tops_2('#skF_5',A_120)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120))))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_135,c_321])).

tff(c_3151,plain,(
    ! [A_397] :
      ( v4_pre_topc('#skF_3'('#skF_6','#skF_5'),A_397)
      | ~ v2_tops_2('#skF_5',A_397)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_397))))
      | ~ l1_pre_topc(A_397)
      | ~ r1_tarski('#skF_3'('#skF_6','#skF_5'),u1_struct_0(A_397)) ) ),
    inference(resolution,[status(thm)],[c_18,c_366])).

tff(c_3160,plain,
    ( v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_4')
    | ~ v2_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ r1_tarski('#skF_3'('#skF_6','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_3151])).

tff(c_3167,plain,(
    v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_44,c_38,c_3160])).

tff(c_3169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_3167])).

tff(c_3170,plain,(
    v4_pre_topc('#skF_3'('#skF_6','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_24,plain,(
    ! [A_15,B_21] :
      ( ~ v4_pre_topc('#skF_3'(A_15,B_21),A_15)
      | v2_tops_2(B_21,A_15)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3173,plain,
    ( v2_tops_2('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_3170,c_24])).

tff(c_3176,plain,(
    v2_tops_2('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_45,c_3173])).

tff(c_3178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.29  
% 6.38/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.29  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 6.47/2.29  
% 6.47/2.29  %Foreground sorts:
% 6.47/2.29  
% 6.47/2.29  
% 6.47/2.29  %Background operators:
% 6.47/2.29  
% 6.47/2.29  
% 6.47/2.29  %Foreground operators:
% 6.47/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.47/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.47/2.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.47/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.47/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.47/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.47/2.29  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 6.47/2.29  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.47/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.47/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.47/2.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.47/2.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.47/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.47/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.47/2.29  
% 6.47/2.31  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v2_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v2_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tops_2)).
% 6.47/2.31  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.47/2.31  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.47/2.31  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 6.47/2.31  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.47/2.31  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.47/2.31  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 6.47/2.31  tff(c_34, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_32, plain, (~v2_tops_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_46, plain, (~v2_tops_2('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 6.47/2.31  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_40, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_53, plain, (![B_55, A_56]: (l1_pre_topc(B_55) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.47/2.31  tff(c_56, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_53])).
% 6.47/2.31  tff(c_59, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 6.47/2.31  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_45, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 6.47/2.31  tff(c_60, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_71, plain, (r1_tarski('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_45, c_60])).
% 6.47/2.31  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_123, plain, (![A_80, B_81]: (r2_hidden('#skF_3'(A_80, B_81), B_81) | v2_tops_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80)))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.47/2.31  tff(c_128, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5') | v2_tops_2('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_45, c_123])).
% 6.47/2.31  tff(c_134, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5') | v2_tops_2('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_128])).
% 6.47/2.31  tff(c_135, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_134])).
% 6.47/2.31  tff(c_14, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.47/2.31  tff(c_143, plain, (![A_84]: (r2_hidden('#skF_3'('#skF_6', '#skF_5'), A_84) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_135, c_14])).
% 6.47/2.31  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.47/2.31  tff(c_152, plain, (![A_85]: (r1_tarski('#skF_3'('#skF_6', '#skF_5'), A_85) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(resolution, [status(thm)], [c_143, c_2])).
% 6.47/2.31  tff(c_164, plain, (r1_tarski('#skF_3'('#skF_6', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_152])).
% 6.47/2.31  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_162, plain, (![A_85]: (r1_tarski('#skF_3'('#skF_6', '#skF_5'), A_85) | ~r1_tarski('#skF_5', k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_18, c_152])).
% 6.47/2.31  tff(c_231, plain, (![D_97, C_98, A_99]: (v4_pre_topc(D_97, C_98) | ~m1_subset_1(D_97, k1_zfmisc_1(u1_struct_0(C_98))) | ~v4_pre_topc(D_97, A_99) | ~m1_pre_topc(C_98, A_99) | ~m1_subset_1(D_97, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.47/2.31  tff(c_483, plain, (![A_133, C_134, A_135]: (v4_pre_topc(A_133, C_134) | ~v4_pre_topc(A_133, A_135) | ~m1_pre_topc(C_134, A_135) | ~m1_subset_1(A_133, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~r1_tarski(A_133, u1_struct_0(C_134)))), inference(resolution, [status(thm)], [c_18, c_231])).
% 6.47/2.31  tff(c_485, plain, (![A_133]: (v4_pre_topc(A_133, '#skF_6') | ~v4_pre_topc(A_133, '#skF_4') | ~m1_subset_1(A_133, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_133, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_40, c_483])).
% 6.47/2.31  tff(c_598, plain, (![A_142]: (v4_pre_topc(A_142, '#skF_6') | ~v4_pre_topc(A_142, '#skF_4') | ~m1_subset_1(A_142, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_142, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_485])).
% 6.47/2.31  tff(c_622, plain, (![A_150]: (v4_pre_topc(A_150, '#skF_6') | ~v4_pre_topc(A_150, '#skF_4') | ~r1_tarski(A_150, u1_struct_0('#skF_6')) | ~r1_tarski(A_150, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_598])).
% 6.47/2.31  tff(c_656, plain, (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_6') | ~v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_3'('#skF_6', '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_162, c_622])).
% 6.47/2.31  tff(c_675, plain, (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_6') | ~v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_164, c_656])).
% 6.47/2.31  tff(c_680, plain, (~v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_675])).
% 6.47/2.31  tff(c_38, plain, (v2_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.31  tff(c_321, plain, (![C_111, A_112, B_113]: (v4_pre_topc(C_111, A_112) | ~r2_hidden(C_111, B_113) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~v2_tops_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.47/2.31  tff(c_366, plain, (![A_120]: (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), A_120) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_5'), k1_zfmisc_1(u1_struct_0(A_120))) | ~v2_tops_2('#skF_5', A_120) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120)))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_135, c_321])).
% 6.47/2.31  tff(c_3151, plain, (![A_397]: (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), A_397) | ~v2_tops_2('#skF_5', A_397) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_397)))) | ~l1_pre_topc(A_397) | ~r1_tarski('#skF_3'('#skF_6', '#skF_5'), u1_struct_0(A_397)))), inference(resolution, [status(thm)], [c_18, c_366])).
% 6.47/2.31  tff(c_3160, plain, (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_4') | ~v2_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_3'('#skF_6', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_3151])).
% 6.47/2.31  tff(c_3167, plain, (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_44, c_38, c_3160])).
% 6.47/2.31  tff(c_3169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_680, c_3167])).
% 6.47/2.31  tff(c_3170, plain, (v4_pre_topc('#skF_3'('#skF_6', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_675])).
% 6.47/2.31  tff(c_24, plain, (![A_15, B_21]: (~v4_pre_topc('#skF_3'(A_15, B_21), A_15) | v2_tops_2(B_21, A_15) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.47/2.31  tff(c_3173, plain, (v2_tops_2('#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_3170, c_24])).
% 6.47/2.31  tff(c_3176, plain, (v2_tops_2('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_45, c_3173])).
% 6.47/2.31  tff(c_3178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_3176])).
% 6.47/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.31  
% 6.47/2.31  Inference rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Ref     : 0
% 6.47/2.31  #Sup     : 714
% 6.47/2.31  #Fact    : 0
% 6.47/2.31  #Define  : 0
% 6.47/2.31  #Split   : 18
% 6.47/2.31  #Chain   : 0
% 6.47/2.31  #Close   : 0
% 6.47/2.31  
% 6.47/2.31  Ordering : KBO
% 6.47/2.31  
% 6.47/2.31  Simplification rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Subsume      : 158
% 6.47/2.31  #Demod        : 99
% 6.47/2.31  #Tautology    : 71
% 6.47/2.31  #SimpNegUnit  : 46
% 6.47/2.31  #BackRed      : 8
% 6.47/2.31  
% 6.47/2.31  #Partial instantiations: 0
% 6.47/2.31  #Strategies tried      : 1
% 6.47/2.31  
% 6.47/2.31  Timing (in seconds)
% 6.47/2.31  ----------------------
% 6.47/2.31  Preprocessing        : 0.31
% 6.47/2.31  Parsing              : 0.16
% 6.47/2.31  CNF conversion       : 0.03
% 6.47/2.31  Main loop            : 1.23
% 6.47/2.31  Inferencing          : 0.43
% 6.47/2.31  Reduction            : 0.30
% 6.47/2.31  Demodulation         : 0.19
% 6.47/2.31  BG Simplification    : 0.04
% 6.47/2.31  Subsumption          : 0.38
% 6.47/2.31  Abstraction          : 0.05
% 6.47/2.31  MUC search           : 0.00
% 6.47/2.31  Cooper               : 0.00
% 6.47/2.31  Total                : 1.57
% 6.47/2.31  Index Insertion      : 0.00
% 6.47/2.31  Index Deletion       : 0.00
% 6.47/2.31  Index Matching       : 0.00
% 6.47/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
