%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   59 (  73 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 182 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_yellow_6 > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_waybel_0(B,A)
           => m1_yellow_6(B,A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_6)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_45,plain,(
    ! [B_32,A_33] :
      ( l1_orders_2(B_32)
      | ~ l1_waybel_0(B_32,A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_51,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [B_56,A_57] :
      ( m1_yellow_0(B_56,A_57)
      | ~ r1_tarski(u1_orders_2(B_56),u1_orders_2(A_57))
      | ~ r1_tarski(u1_struct_0(B_56),u1_struct_0(A_57))
      | ~ l1_orders_2(B_56)
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    ! [B_56] :
      ( m1_yellow_0(B_56,B_56)
      | ~ r1_tarski(u1_orders_2(B_56),u1_orders_2(B_56))
      | ~ l1_orders_2(B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_90,plain,(
    ! [B_56] :
      ( m1_yellow_0(B_56,B_56)
      | ~ l1_orders_2(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( v1_funct_1(u1_waybel_0(A_21,B_22))
      | ~ l1_waybel_0(B_22,A_21)
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( v1_funct_2(u1_waybel_0(A_21,B_22),u1_struct_0(B_22),u1_struct_0(A_21))
      | ~ l1_waybel_0(B_22,A_21)
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(u1_waybel_0(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_22),u1_struct_0(A_21))))
      | ~ l1_waybel_0(B_22,A_21)
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_80,B_81,D_82,C_83] :
      ( r2_relset_1(A_80,B_81,k2_partfun1(A_80,B_81,D_82,C_83),D_82)
      | ~ r1_tarski(A_80,C_83)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(D_82,A_80,B_81)
      | ~ v1_funct_1(D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,(
    ! [B_116,A_117,C_118] :
      ( r2_relset_1(u1_struct_0(B_116),u1_struct_0(A_117),k2_partfun1(u1_struct_0(B_116),u1_struct_0(A_117),u1_waybel_0(A_117,B_116),C_118),u1_waybel_0(A_117,B_116))
      | ~ r1_tarski(u1_struct_0(B_116),C_118)
      | ~ v1_funct_2(u1_waybel_0(A_117,B_116),u1_struct_0(B_116),u1_struct_0(A_117))
      | ~ v1_funct_1(u1_waybel_0(A_117,B_116))
      | ~ l1_waybel_0(B_116,A_117)
      | ~ l1_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_10,plain,(
    ! [D_6,C_5,A_3,B_4] :
      ( D_6 = C_5
      | ~ r2_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(D_6,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_271,plain,(
    ! [B_152,A_153,C_154] :
      ( k2_partfun1(u1_struct_0(B_152),u1_struct_0(A_153),u1_waybel_0(A_153,B_152),C_154) = u1_waybel_0(A_153,B_152)
      | ~ m1_subset_1(u1_waybel_0(A_153,B_152),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_152),u1_struct_0(A_153))))
      | ~ m1_subset_1(k2_partfun1(u1_struct_0(B_152),u1_struct_0(A_153),u1_waybel_0(A_153,B_152),C_154),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_152),u1_struct_0(A_153))))
      | ~ r1_tarski(u1_struct_0(B_152),C_154)
      | ~ v1_funct_2(u1_waybel_0(A_153,B_152),u1_struct_0(B_152),u1_struct_0(A_153))
      | ~ v1_funct_1(u1_waybel_0(A_153,B_152))
      | ~ l1_waybel_0(B_152,A_153)
      | ~ l1_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_213,c_10])).

tff(c_280,plain,(
    ! [B_155,A_156,D_157] :
      ( k2_partfun1(u1_struct_0(B_155),u1_struct_0(A_156),u1_waybel_0(A_156,B_155),D_157) = u1_waybel_0(A_156,B_155)
      | ~ r1_tarski(u1_struct_0(B_155),D_157)
      | ~ v1_funct_2(u1_waybel_0(A_156,B_155),u1_struct_0(B_155),u1_struct_0(A_156))
      | ~ l1_waybel_0(B_155,A_156)
      | ~ l1_struct_0(A_156)
      | ~ m1_subset_1(u1_waybel_0(A_156,B_155),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_155),u1_struct_0(A_156))))
      | ~ v1_funct_1(u1_waybel_0(A_156,B_155)) ) ),
    inference(resolution,[status(thm)],[c_12,c_271])).

tff(c_288,plain,(
    ! [B_158,A_159,D_160] :
      ( k2_partfun1(u1_struct_0(B_158),u1_struct_0(A_159),u1_waybel_0(A_159,B_158),D_160) = u1_waybel_0(A_159,B_158)
      | ~ r1_tarski(u1_struct_0(B_158),D_160)
      | ~ v1_funct_2(u1_waybel_0(A_159,B_158),u1_struct_0(B_158),u1_struct_0(A_159))
      | ~ v1_funct_1(u1_waybel_0(A_159,B_158))
      | ~ l1_waybel_0(B_158,A_159)
      | ~ l1_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_26,c_280])).

tff(c_292,plain,(
    ! [B_161,A_162,D_163] :
      ( k2_partfun1(u1_struct_0(B_161),u1_struct_0(A_162),u1_waybel_0(A_162,B_161),D_163) = u1_waybel_0(A_162,B_161)
      | ~ r1_tarski(u1_struct_0(B_161),D_163)
      | ~ v1_funct_1(u1_waybel_0(A_162,B_161))
      | ~ l1_waybel_0(B_161,A_162)
      | ~ l1_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_28,c_288])).

tff(c_32,plain,(
    ! [C_29,A_23,B_27] :
      ( m1_yellow_6(C_29,A_23,B_27)
      | k2_partfun1(u1_struct_0(B_27),u1_struct_0(A_23),u1_waybel_0(A_23,B_27),u1_struct_0(C_29)) != u1_waybel_0(A_23,C_29)
      | ~ m1_yellow_0(C_29,B_27)
      | ~ l1_waybel_0(C_29,A_23)
      | ~ l1_waybel_0(B_27,A_23)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_354,plain,(
    ! [C_167,A_168,B_169] :
      ( m1_yellow_6(C_167,A_168,B_169)
      | u1_waybel_0(A_168,C_167) != u1_waybel_0(A_168,B_169)
      | ~ m1_yellow_0(C_167,B_169)
      | ~ l1_waybel_0(C_167,A_168)
      | ~ l1_waybel_0(B_169,A_168)
      | ~ l1_struct_0(A_168)
      | ~ r1_tarski(u1_struct_0(B_169),u1_struct_0(C_167))
      | ~ v1_funct_1(u1_waybel_0(A_168,B_169))
      | ~ l1_waybel_0(B_169,A_168)
      | ~ l1_struct_0(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_32])).

tff(c_362,plain,(
    ! [B_170,A_171] :
      ( m1_yellow_6(B_170,A_171,B_170)
      | ~ m1_yellow_0(B_170,B_170)
      | ~ v1_funct_1(u1_waybel_0(A_171,B_170))
      | ~ l1_waybel_0(B_170,A_171)
      | ~ l1_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_6,c_354])).

tff(c_366,plain,(
    ! [B_172,A_173] :
      ( m1_yellow_6(B_172,A_173,B_172)
      | ~ m1_yellow_0(B_172,B_172)
      | ~ l1_waybel_0(B_172,A_173)
      | ~ l1_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_30,c_362])).

tff(c_38,plain,(
    ~ m1_yellow_6('#skF_2','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_374,plain,
    ( ~ m1_yellow_0('#skF_2','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_38])).

tff(c_382,plain,(
    ~ m1_yellow_0('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_374])).

tff(c_385,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.36  
% 2.82/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.36  %$ r2_relset_1 > v1_funct_2 > m1_yellow_6 > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.82/1.36  
% 2.82/1.36  %Foreground sorts:
% 2.82/1.36  
% 2.82/1.36  
% 2.82/1.36  %Background operators:
% 2.82/1.36  
% 2.82/1.36  
% 2.82/1.36  %Foreground operators:
% 2.82/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.82/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.36  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.82/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.82/1.36  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.82/1.36  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.82/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.36  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.82/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.36  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.82/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.82/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.36  
% 2.82/1.38  tff(f_107, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => m1_yellow_6(B, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_6)).
% 2.82/1.38  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.82/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.82/1.38  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_yellow_0)).
% 2.82/1.38  tff(f_85, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.82/1.38  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 2.82/1.38  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.82/1.38  tff(f_39, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.82/1.38  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_yellow_6)).
% 2.82/1.38  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.82/1.38  tff(c_40, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.82/1.38  tff(c_45, plain, (![B_32, A_33]: (l1_orders_2(B_32) | ~l1_waybel_0(B_32, A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.38  tff(c_48, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_45])).
% 2.82/1.38  tff(c_51, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_48])).
% 2.82/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.38  tff(c_79, plain, (![B_56, A_57]: (m1_yellow_0(B_56, A_57) | ~r1_tarski(u1_orders_2(B_56), u1_orders_2(A_57)) | ~r1_tarski(u1_struct_0(B_56), u1_struct_0(A_57)) | ~l1_orders_2(B_56) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.38  tff(c_86, plain, (![B_56]: (m1_yellow_0(B_56, B_56) | ~r1_tarski(u1_orders_2(B_56), u1_orders_2(B_56)) | ~l1_orders_2(B_56))), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.82/1.38  tff(c_90, plain, (![B_56]: (m1_yellow_0(B_56, B_56) | ~l1_orders_2(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_86])).
% 2.82/1.38  tff(c_30, plain, (![A_21, B_22]: (v1_funct_1(u1_waybel_0(A_21, B_22)) | ~l1_waybel_0(B_22, A_21) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.82/1.38  tff(c_28, plain, (![A_21, B_22]: (v1_funct_2(u1_waybel_0(A_21, B_22), u1_struct_0(B_22), u1_struct_0(A_21)) | ~l1_waybel_0(B_22, A_21) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.82/1.38  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(u1_waybel_0(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_22), u1_struct_0(A_21)))) | ~l1_waybel_0(B_22, A_21) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.82/1.38  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k2_partfun1(A_7, B_8, C_9, D_10), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.38  tff(c_138, plain, (![A_80, B_81, D_82, C_83]: (r2_relset_1(A_80, B_81, k2_partfun1(A_80, B_81, D_82, C_83), D_82) | ~r1_tarski(A_80, C_83) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(D_82, A_80, B_81) | ~v1_funct_1(D_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.38  tff(c_213, plain, (![B_116, A_117, C_118]: (r2_relset_1(u1_struct_0(B_116), u1_struct_0(A_117), k2_partfun1(u1_struct_0(B_116), u1_struct_0(A_117), u1_waybel_0(A_117, B_116), C_118), u1_waybel_0(A_117, B_116)) | ~r1_tarski(u1_struct_0(B_116), C_118) | ~v1_funct_2(u1_waybel_0(A_117, B_116), u1_struct_0(B_116), u1_struct_0(A_117)) | ~v1_funct_1(u1_waybel_0(A_117, B_116)) | ~l1_waybel_0(B_116, A_117) | ~l1_struct_0(A_117))), inference(resolution, [status(thm)], [c_26, c_138])).
% 2.82/1.38  tff(c_10, plain, (![D_6, C_5, A_3, B_4]: (D_6=C_5 | ~r2_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(D_6, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.38  tff(c_271, plain, (![B_152, A_153, C_154]: (k2_partfun1(u1_struct_0(B_152), u1_struct_0(A_153), u1_waybel_0(A_153, B_152), C_154)=u1_waybel_0(A_153, B_152) | ~m1_subset_1(u1_waybel_0(A_153, B_152), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_152), u1_struct_0(A_153)))) | ~m1_subset_1(k2_partfun1(u1_struct_0(B_152), u1_struct_0(A_153), u1_waybel_0(A_153, B_152), C_154), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_152), u1_struct_0(A_153)))) | ~r1_tarski(u1_struct_0(B_152), C_154) | ~v1_funct_2(u1_waybel_0(A_153, B_152), u1_struct_0(B_152), u1_struct_0(A_153)) | ~v1_funct_1(u1_waybel_0(A_153, B_152)) | ~l1_waybel_0(B_152, A_153) | ~l1_struct_0(A_153))), inference(resolution, [status(thm)], [c_213, c_10])).
% 2.82/1.38  tff(c_280, plain, (![B_155, A_156, D_157]: (k2_partfun1(u1_struct_0(B_155), u1_struct_0(A_156), u1_waybel_0(A_156, B_155), D_157)=u1_waybel_0(A_156, B_155) | ~r1_tarski(u1_struct_0(B_155), D_157) | ~v1_funct_2(u1_waybel_0(A_156, B_155), u1_struct_0(B_155), u1_struct_0(A_156)) | ~l1_waybel_0(B_155, A_156) | ~l1_struct_0(A_156) | ~m1_subset_1(u1_waybel_0(A_156, B_155), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_155), u1_struct_0(A_156)))) | ~v1_funct_1(u1_waybel_0(A_156, B_155)))), inference(resolution, [status(thm)], [c_12, c_271])).
% 2.82/1.38  tff(c_288, plain, (![B_158, A_159, D_160]: (k2_partfun1(u1_struct_0(B_158), u1_struct_0(A_159), u1_waybel_0(A_159, B_158), D_160)=u1_waybel_0(A_159, B_158) | ~r1_tarski(u1_struct_0(B_158), D_160) | ~v1_funct_2(u1_waybel_0(A_159, B_158), u1_struct_0(B_158), u1_struct_0(A_159)) | ~v1_funct_1(u1_waybel_0(A_159, B_158)) | ~l1_waybel_0(B_158, A_159) | ~l1_struct_0(A_159))), inference(resolution, [status(thm)], [c_26, c_280])).
% 2.82/1.38  tff(c_292, plain, (![B_161, A_162, D_163]: (k2_partfun1(u1_struct_0(B_161), u1_struct_0(A_162), u1_waybel_0(A_162, B_161), D_163)=u1_waybel_0(A_162, B_161) | ~r1_tarski(u1_struct_0(B_161), D_163) | ~v1_funct_1(u1_waybel_0(A_162, B_161)) | ~l1_waybel_0(B_161, A_162) | ~l1_struct_0(A_162))), inference(resolution, [status(thm)], [c_28, c_288])).
% 2.82/1.38  tff(c_32, plain, (![C_29, A_23, B_27]: (m1_yellow_6(C_29, A_23, B_27) | k2_partfun1(u1_struct_0(B_27), u1_struct_0(A_23), u1_waybel_0(A_23, B_27), u1_struct_0(C_29))!=u1_waybel_0(A_23, C_29) | ~m1_yellow_0(C_29, B_27) | ~l1_waybel_0(C_29, A_23) | ~l1_waybel_0(B_27, A_23) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.82/1.38  tff(c_354, plain, (![C_167, A_168, B_169]: (m1_yellow_6(C_167, A_168, B_169) | u1_waybel_0(A_168, C_167)!=u1_waybel_0(A_168, B_169) | ~m1_yellow_0(C_167, B_169) | ~l1_waybel_0(C_167, A_168) | ~l1_waybel_0(B_169, A_168) | ~l1_struct_0(A_168) | ~r1_tarski(u1_struct_0(B_169), u1_struct_0(C_167)) | ~v1_funct_1(u1_waybel_0(A_168, B_169)) | ~l1_waybel_0(B_169, A_168) | ~l1_struct_0(A_168))), inference(superposition, [status(thm), theory('equality')], [c_292, c_32])).
% 2.82/1.38  tff(c_362, plain, (![B_170, A_171]: (m1_yellow_6(B_170, A_171, B_170) | ~m1_yellow_0(B_170, B_170) | ~v1_funct_1(u1_waybel_0(A_171, B_170)) | ~l1_waybel_0(B_170, A_171) | ~l1_struct_0(A_171))), inference(resolution, [status(thm)], [c_6, c_354])).
% 2.82/1.38  tff(c_366, plain, (![B_172, A_173]: (m1_yellow_6(B_172, A_173, B_172) | ~m1_yellow_0(B_172, B_172) | ~l1_waybel_0(B_172, A_173) | ~l1_struct_0(A_173))), inference(resolution, [status(thm)], [c_30, c_362])).
% 2.82/1.38  tff(c_38, plain, (~m1_yellow_6('#skF_2', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.82/1.38  tff(c_374, plain, (~m1_yellow_0('#skF_2', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_366, c_38])).
% 2.82/1.38  tff(c_382, plain, (~m1_yellow_0('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_374])).
% 2.82/1.38  tff(c_385, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_90, c_382])).
% 2.82/1.38  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_385])).
% 2.82/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  Inference rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Ref     : 0
% 2.82/1.38  #Sup     : 83
% 2.82/1.38  #Fact    : 0
% 2.82/1.38  #Define  : 0
% 2.82/1.38  #Split   : 0
% 2.82/1.38  #Chain   : 0
% 2.82/1.38  #Close   : 0
% 2.82/1.38  
% 2.82/1.38  Ordering : KBO
% 2.82/1.38  
% 2.82/1.38  Simplification rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Subsume      : 24
% 2.82/1.38  #Demod        : 8
% 2.82/1.38  #Tautology    : 17
% 2.82/1.38  #SimpNegUnit  : 0
% 2.82/1.38  #BackRed      : 0
% 2.82/1.38  
% 2.82/1.38  #Partial instantiations: 0
% 2.82/1.38  #Strategies tried      : 1
% 2.82/1.38  
% 2.82/1.38  Timing (in seconds)
% 2.82/1.38  ----------------------
% 2.82/1.38  Preprocessing        : 0.30
% 2.82/1.38  Parsing              : 0.17
% 2.82/1.38  CNF conversion       : 0.02
% 2.82/1.38  Main loop            : 0.32
% 2.82/1.38  Inferencing          : 0.14
% 2.82/1.38  Reduction            : 0.07
% 2.82/1.38  Demodulation         : 0.05
% 2.82/1.38  BG Simplification    : 0.02
% 2.82/1.38  Subsumption          : 0.07
% 2.82/1.38  Abstraction          : 0.01
% 2.82/1.38  MUC search           : 0.00
% 2.82/1.38  Cooper               : 0.00
% 2.82/1.38  Total                : 0.65
% 2.82/1.38  Index Insertion      : 0.00
% 2.82/1.38  Index Deletion       : 0.00
% 2.82/1.38  Index Matching       : 0.00
% 2.82/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
