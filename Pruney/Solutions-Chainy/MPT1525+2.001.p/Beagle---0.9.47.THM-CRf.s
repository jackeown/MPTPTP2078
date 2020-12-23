%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:55 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  114 (2331 expanded)
%              Number of leaves         :   27 ( 781 expanded)
%              Depth                    :   34
%              Number of atoms          :  342 (7165 expanded)
%              Number of equality atoms :   21 (1929 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r2_hidden > m1_subset_1 > v3_lattice3 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
                & v3_lattice3(A) )
             => v3_lattice3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_0)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r2_lattice3(A,B,C)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(c_32,plain,(
    ~ v3_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v3_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_8] :
      ( m1_subset_1(u1_orders_2(A_8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8),u1_struct_0(A_8))))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ! [C_59,A_60,D_61,B_62] :
      ( C_59 = A_60
      | g1_orders_2(C_59,D_61) != g1_orders_2(A_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_zfmisc_1(A_60,A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_57,plain,(
    ! [A_63,B_64] :
      ( u1_struct_0('#skF_5') = A_63
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_zfmisc_1(A_63,A_63))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_52])).

tff(c_61,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_74,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_61])).

tff(c_76,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_74])).

tff(c_22,plain,(
    ! [A_15,B_30] :
      ( m1_subset_1('#skF_1'(A_15,B_30),u1_struct_0(A_15))
      | ~ v3_lattice3(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_97,plain,(
    ! [B_30] :
      ( m1_subset_1('#skF_1'('#skF_5',B_30),u1_struct_0('#skF_6'))
      | ~ v3_lattice3('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_105,plain,(
    ! [B_30] : m1_subset_1('#skF_1'('#skF_5',B_30),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_97])).

tff(c_20,plain,(
    ! [A_15,B_30] :
      ( r2_lattice3(A_15,B_30,'#skF_1'(A_15,B_30))
      | ~ v3_lattice3(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_41,B_48,C_49] :
      ( m1_subset_1('#skF_4'(A_41,B_48,C_49),u1_struct_0(A_41))
      | r2_lattice3(A_41,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_41,B_48,C_49] :
      ( r2_hidden('#skF_4'(A_41,B_48,C_49),B_48)
      | r2_lattice3(A_41,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_285,plain,(
    ! [A_117,D_118,C_119,B_120] :
      ( r1_orders_2(A_117,D_118,C_119)
      | ~ r2_hidden(D_118,B_120)
      | ~ m1_subset_1(D_118,u1_struct_0(A_117))
      | ~ r2_lattice3(A_117,B_120,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_344,plain,(
    ! [B_136,A_137,C_134,C_138,A_135] :
      ( r1_orders_2(A_137,'#skF_4'(A_135,B_136,C_138),C_134)
      | ~ m1_subset_1('#skF_4'(A_135,B_136,C_138),u1_struct_0(A_137))
      | ~ r2_lattice3(A_137,B_136,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | r2_lattice3(A_135,B_136,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135) ) ),
    inference(resolution,[status(thm)],[c_28,c_285])).

tff(c_350,plain,(
    ! [A_135,B_136,C_138,C_134] :
      ( r1_orders_2('#skF_5','#skF_4'(A_135,B_136,C_138),C_134)
      | ~ m1_subset_1('#skF_4'(A_135,B_136,C_138),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_5',B_136,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r2_lattice3(A_135,B_136,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_344])).

tff(c_429,plain,(
    ! [A_163,B_164,C_165,C_166] :
      ( r1_orders_2('#skF_5','#skF_4'(A_163,B_164,C_165),C_166)
      | ~ m1_subset_1('#skF_4'(A_163,B_164,C_165),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_5',B_164,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0('#skF_6'))
      | r2_lattice3(A_163,B_164,C_165)
      | ~ m1_subset_1(C_165,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_350])).

tff(c_434,plain,(
    ! [B_48,C_49,C_166] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_6',B_48,C_49),C_166)
      | ~ r2_lattice3('#skF_5',B_48,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_6',B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_429])).

tff(c_458,plain,(
    ! [B_170,C_171,C_172] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_6',B_170,C_171),C_172)
      | ~ r2_lattice3('#skF_5',B_170,C_172)
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_6',B_170,C_171)
      | ~ m1_subset_1(C_171,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_434])).

tff(c_91,plain,
    ( m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_101,plain,(
    m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_91])).

tff(c_87,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_8,plain,(
    ! [D_14,B_10,C_13,A_9] :
      ( D_14 = B_10
      | g1_orders_2(C_13,D_14) != g1_orders_2(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k2_zfmisc_1(A_9,A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_5') = D_14
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_8])).

tff(c_122,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_5') = D_14
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_114])).

tff(c_140,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_122])).

tff(c_201,plain,(
    ! [B_104,C_105,A_106] :
      ( r2_hidden(k4_tarski(B_104,C_105),u1_orders_2(A_106))
      | ~ r1_orders_2(A_106,B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_106))
      | ~ m1_subset_1(B_104,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_211,plain,(
    ! [B_104,C_105] :
      ( r2_hidden(k4_tarski(B_104,C_105),u1_orders_2('#skF_6'))
      | ~ r1_orders_2('#skF_5',B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_201])).

tff(c_254,plain,(
    ! [B_111,C_112] :
      ( r2_hidden(k4_tarski(B_111,C_112),u1_orders_2('#skF_6'))
      | ~ r1_orders_2('#skF_5',B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_76,c_211])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( r1_orders_2(A_1,B_5,C_7)
      | ~ r2_hidden(k4_tarski(B_5,C_7),u1_orders_2(A_1))
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_260,plain,(
    ! [B_111,C_112] :
      ( r1_orders_2('#skF_6',B_111,C_112)
      | ~ l1_orders_2('#skF_6')
      | ~ r1_orders_2('#skF_5',B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_254,c_2])).

tff(c_264,plain,(
    ! [B_111,C_112] :
      ( r1_orders_2('#skF_6',B_111,C_112)
      | ~ r1_orders_2('#skF_5',B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_260])).

tff(c_468,plain,(
    ! [B_173,C_174,C_175] :
      ( r1_orders_2('#skF_6','#skF_4'('#skF_6',B_173,C_174),C_175)
      | ~ m1_subset_1('#skF_4'('#skF_6',B_173,C_174),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_5',B_173,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_6',B_173,C_174)
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_458,c_264])).

tff(c_471,plain,(
    ! [B_48,C_49,C_175] :
      ( r1_orders_2('#skF_6','#skF_4'('#skF_6',B_48,C_49),C_175)
      | ~ r2_lattice3('#skF_5',B_48,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_6',B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_468])).

tff(c_480,plain,(
    ! [B_179,C_180,C_181] :
      ( r1_orders_2('#skF_6','#skF_4'('#skF_6',B_179,C_180),C_181)
      | ~ r2_lattice3('#skF_5',B_179,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_6',B_179,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_471])).

tff(c_26,plain,(
    ! [A_41,B_48,C_49] :
      ( ~ r1_orders_2(A_41,'#skF_4'(A_41,B_48,C_49),C_49)
      | r2_lattice3(A_41,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_487,plain,(
    ! [B_179,C_181] :
      ( ~ l1_orders_2('#skF_6')
      | ~ r2_lattice3('#skF_5',B_179,C_181)
      | r2_lattice3('#skF_6',B_179,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_480,c_26])).

tff(c_495,plain,(
    ! [B_182,C_183] :
      ( ~ r2_lattice3('#skF_5',B_182,C_183)
      | r2_lattice3('#skF_6',B_182,C_183)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_487])).

tff(c_503,plain,(
    ! [B_30] :
      ( r2_lattice3('#skF_6',B_30,'#skF_1'('#skF_5',B_30))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_30),u1_struct_0('#skF_6'))
      | ~ v3_lattice3('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_495])).

tff(c_512,plain,(
    ! [B_30] : r2_lattice3('#skF_6',B_30,'#skF_1'('#skF_5',B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_105,c_503])).

tff(c_14,plain,(
    ! [A_15,C_39] :
      ( r2_lattice3(A_15,'#skF_2'(A_15),'#skF_3'(A_15,C_39))
      | v3_lattice3(A_15)
      | ~ r2_lattice3(A_15,'#skF_2'(A_15),C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_15,C_39] :
      ( m1_subset_1('#skF_3'(A_15,C_39),u1_struct_0(A_15))
      | v3_lattice3(A_15)
      | ~ r2_lattice3(A_15,'#skF_2'(A_15),C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_513,plain,(
    ! [B_184] : r2_lattice3('#skF_6',B_184,'#skF_1'('#skF_5',B_184)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_105,c_503])).

tff(c_194,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_orders_2(A_99,B_100,C_101)
      | ~ r2_hidden(k4_tarski(B_100,C_101),u1_orders_2(A_99))
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [B_100,C_101] :
      ( r1_orders_2('#skF_5',B_100,C_101)
      | ~ r2_hidden(k4_tarski(B_100,C_101),u1_orders_2('#skF_6'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_194])).

tff(c_199,plain,(
    ! [B_100,C_101] :
      ( r1_orders_2('#skF_5',B_100,C_101)
      | ~ r2_hidden(k4_tarski(B_100,C_101),u1_orders_2('#skF_6'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_76,c_197])).

tff(c_205,plain,(
    ! [B_104,C_105] :
      ( r1_orders_2('#skF_5',B_104,C_105)
      | ~ r1_orders_2('#skF_6',B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_201,c_199])).

tff(c_220,plain,(
    ! [B_107,C_108] :
      ( r1_orders_2('#skF_5',B_107,C_108)
      | ~ r1_orders_2('#skF_6',B_107,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_205])).

tff(c_223,plain,(
    ! [B_107,C_39] :
      ( r1_orders_2('#skF_5',B_107,'#skF_3'('#skF_6',C_39))
      | ~ r1_orders_2('#skF_6',B_107,'#skF_3'('#skF_6',C_39))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_6'))
      | v3_lattice3('#skF_6')
      | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),C_39)
      | ~ m1_subset_1(C_39,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_16,c_220])).

tff(c_236,plain,(
    ! [B_107,C_39] :
      ( r1_orders_2('#skF_5',B_107,'#skF_3'('#skF_6',C_39))
      | ~ r1_orders_2('#skF_6',B_107,'#skF_3'('#skF_6',C_39))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_6'))
      | v3_lattice3('#skF_6')
      | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),C_39)
      | ~ m1_subset_1(C_39,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_223])).

tff(c_237,plain,(
    ! [B_107,C_39] :
      ( r1_orders_2('#skF_5',B_107,'#skF_3'('#skF_6',C_39))
      | ~ r1_orders_2('#skF_6',B_107,'#skF_3'('#skF_6',C_39))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),C_39)
      | ~ m1_subset_1(C_39,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_236])).

tff(c_516,plain,(
    ! [B_107] :
      ( r1_orders_2('#skF_5',B_107,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ r1_orders_2('#skF_6',B_107,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_2'('#skF_6')),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_513,c_237])).

tff(c_528,plain,(
    ! [B_186] :
      ( r1_orders_2('#skF_5',B_186,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ r1_orders_2('#skF_6',B_186,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_516])).

tff(c_534,plain,(
    ! [B_48] :
      ( r2_lattice3('#skF_5',B_48,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_6','#skF_4'('#skF_5',B_48,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_48,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_528,c_26])).

tff(c_538,plain,(
    ! [B_48] :
      ( r2_lattice3('#skF_5',B_48,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_6'))
      | ~ r1_orders_2('#skF_6','#skF_4'('#skF_5',B_48,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_48,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_534])).

tff(c_632,plain,(
    ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_641,plain,
    ( v3_lattice3('#skF_6')
    | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_1'('#skF_5','#skF_2'('#skF_6')))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_2'('#skF_6')),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_632])).

tff(c_644,plain,(
    v3_lattice3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_105,c_512,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_644])).

tff(c_648,plain,(
    m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_165,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1('#skF_4'(A_83,B_84,C_85),u1_struct_0(A_83))
      | r2_lattice3(A_83,B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_168,plain,(
    ! [B_84,C_85] :
      ( m1_subset_1('#skF_4'('#skF_5',B_84,C_85),u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_5',B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_165])).

tff(c_170,plain,(
    ! [B_84,C_85] :
      ( m1_subset_1('#skF_4'('#skF_5',B_84,C_85),u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_5',B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_168])).

tff(c_346,plain,(
    ! [B_84,C_85,C_134] :
      ( r1_orders_2('#skF_6','#skF_4'('#skF_5',B_84,C_85),C_134)
      | ~ r2_lattice3('#skF_6',B_84,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1(C_85,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r2_lattice3('#skF_5',B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_170,c_344])).

tff(c_353,plain,(
    ! [B_84,C_85,C_134] :
      ( r1_orders_2('#skF_6','#skF_4'('#skF_5',B_84,C_85),C_134)
      | ~ r2_lattice3('#skF_6',B_84,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_6'))
      | r2_lattice3('#skF_5',B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_38,c_346])).

tff(c_652,plain,(
    ! [B_235] :
      ( r2_lattice3('#skF_5',B_235,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ r1_orders_2('#skF_6','#skF_4'('#skF_5',B_235,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_235,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_660,plain,(
    ! [B_84] :
      ( ~ m1_subset_1('#skF_4'('#skF_5',B_84,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_6',B_84,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | r2_lattice3('#skF_5',B_84,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_353,c_652])).

tff(c_667,plain,(
    ! [B_236] :
      ( ~ m1_subset_1('#skF_4'('#skF_5',B_236,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_6',B_236,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | r2_lattice3('#skF_5',B_236,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_660])).

tff(c_671,plain,(
    ! [B_84] :
      ( ~ r2_lattice3('#skF_6',B_84,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | r2_lattice3('#skF_5',B_84,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_170,c_667])).

tff(c_675,plain,(
    ! [B_237] :
      ( ~ r2_lattice3('#skF_6',B_237,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))))
      | r2_lattice3('#skF_5',B_237,'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_671])).

tff(c_18,plain,(
    ! [A_15,B_30,D_35] :
      ( r1_orders_2(A_15,'#skF_1'(A_15,B_30),D_35)
      | ~ r2_lattice3(A_15,B_30,D_35)
      | ~ m1_subset_1(D_35,u1_struct_0(A_15))
      | ~ v3_lattice3(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_265,plain,(
    ! [B_113,C_114] :
      ( r1_orders_2('#skF_6',B_113,C_114)
      | ~ r1_orders_2('#skF_5',B_113,C_114)
      | ~ m1_subset_1(C_114,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_260])).

tff(c_270,plain,(
    ! [B_30,D_35] :
      ( r1_orders_2('#skF_6','#skF_1'('#skF_5',B_30),D_35)
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_30),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_5',B_30,D_35)
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_5'))
      | ~ v3_lattice3('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_265])).

tff(c_277,plain,(
    ! [B_115,D_116] :
      ( r1_orders_2('#skF_6','#skF_1'('#skF_5',B_115),D_116)
      | ~ r2_lattice3('#skF_5',B_115,D_116)
      | ~ m1_subset_1(D_116,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_76,c_105,c_270])).

tff(c_12,plain,(
    ! [A_15,C_39] :
      ( ~ r1_orders_2(A_15,C_39,'#skF_3'(A_15,C_39))
      | v3_lattice3(A_15)
      | ~ r2_lattice3(A_15,'#skF_2'(A_15),C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_280,plain,(
    ! [B_115] :
      ( v3_lattice3('#skF_6')
      | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_1'('#skF_5',B_115))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_115),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ r2_lattice3('#skF_5',B_115,'#skF_3'('#skF_6','#skF_1'('#skF_5',B_115)))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5',B_115)),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_277,c_12])).

tff(c_283,plain,(
    ! [B_115] :
      ( v3_lattice3('#skF_6')
      | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_1'('#skF_5',B_115))
      | ~ r2_lattice3('#skF_5',B_115,'#skF_3'('#skF_6','#skF_1'('#skF_5',B_115)))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5',B_115)),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_105,c_280])).

tff(c_284,plain,(
    ! [B_115] :
      ( ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_1'('#skF_5',B_115))
      | ~ r2_lattice3('#skF_5',B_115,'#skF_3'('#skF_6','#skF_1'('#skF_5',B_115)))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5',B_115)),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_283])).

tff(c_680,plain,
    ( ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_1'('#skF_5','#skF_2'('#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6'))),u1_struct_0('#skF_6'))
    | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))) ),
    inference(resolution,[status(thm)],[c_675,c_284])).

tff(c_686,plain,(
    ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_3'('#skF_6','#skF_1'('#skF_5','#skF_2'('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_512,c_680])).

tff(c_695,plain,
    ( v3_lattice3('#skF_6')
    | ~ r2_lattice3('#skF_6','#skF_2'('#skF_6'),'#skF_1'('#skF_5','#skF_2'('#skF_6')))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_2'('#skF_6')),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_686])).

tff(c_698,plain,(
    v3_lattice3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_105,c_512,c_695])).

tff(c_700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  %$ r2_lattice3 > r1_orders_2 > r2_hidden > m1_subset_1 > v3_lattice3 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_1
% 3.22/1.50  
% 3.22/1.50  %Foreground sorts:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Background operators:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Foreground operators:
% 3.22/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.22/1.50  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.22/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.22/1.50  tff(v3_lattice3, type, v3_lattice3: $i > $o).
% 3.22/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.22/1.50  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.22/1.50  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 3.22/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.50  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.22/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.50  
% 3.22/1.53  tff(f_93, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(B), u1_orders_2(B))) & v3_lattice3(A)) => v3_lattice3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_0)).
% 3.22/1.53  tff(f_41, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.22/1.53  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 3.22/1.53  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (v3_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r2_lattice3(A, B, C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_lattice3)).
% 3.22/1.53  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 3.22/1.53  tff(f_37, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 3.22/1.53  tff(c_32, plain, (~v3_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.22/1.53  tff(c_38, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.22/1.53  tff(c_40, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.22/1.53  tff(c_34, plain, (v3_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.22/1.53  tff(c_6, plain, (![A_8]: (m1_subset_1(u1_orders_2(A_8), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8), u1_struct_0(A_8)))) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.53  tff(c_36, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))=g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.22/1.53  tff(c_52, plain, (![C_59, A_60, D_61, B_62]: (C_59=A_60 | g1_orders_2(C_59, D_61)!=g1_orders_2(A_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.53  tff(c_57, plain, (![A_63, B_64]: (u1_struct_0('#skF_5')=A_63 | g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))!=g1_orders_2(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k2_zfmisc_1(A_63, A_63))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_52])).
% 3.22/1.53  tff(c_61, plain, (![A_8]: (u1_struct_0(A_8)=u1_struct_0('#skF_5') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_57])).
% 3.22/1.53  tff(c_74, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~l1_orders_2('#skF_6')), inference(reflexivity, [status(thm), theory('equality')], [c_61])).
% 3.22/1.53  tff(c_76, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_74])).
% 3.22/1.53  tff(c_22, plain, (![A_15, B_30]: (m1_subset_1('#skF_1'(A_15, B_30), u1_struct_0(A_15)) | ~v3_lattice3(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_97, plain, (![B_30]: (m1_subset_1('#skF_1'('#skF_5', B_30), u1_struct_0('#skF_6')) | ~v3_lattice3('#skF_5') | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_22])).
% 3.22/1.53  tff(c_105, plain, (![B_30]: (m1_subset_1('#skF_1'('#skF_5', B_30), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_97])).
% 3.22/1.53  tff(c_20, plain, (![A_15, B_30]: (r2_lattice3(A_15, B_30, '#skF_1'(A_15, B_30)) | ~v3_lattice3(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_30, plain, (![A_41, B_48, C_49]: (m1_subset_1('#skF_4'(A_41, B_48, C_49), u1_struct_0(A_41)) | r2_lattice3(A_41, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_41)) | ~l1_orders_2(A_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.53  tff(c_28, plain, (![A_41, B_48, C_49]: (r2_hidden('#skF_4'(A_41, B_48, C_49), B_48) | r2_lattice3(A_41, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_41)) | ~l1_orders_2(A_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.53  tff(c_285, plain, (![A_117, D_118, C_119, B_120]: (r1_orders_2(A_117, D_118, C_119) | ~r2_hidden(D_118, B_120) | ~m1_subset_1(D_118, u1_struct_0(A_117)) | ~r2_lattice3(A_117, B_120, C_119) | ~m1_subset_1(C_119, u1_struct_0(A_117)) | ~l1_orders_2(A_117))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.53  tff(c_344, plain, (![B_136, A_137, C_134, C_138, A_135]: (r1_orders_2(A_137, '#skF_4'(A_135, B_136, C_138), C_134) | ~m1_subset_1('#skF_4'(A_135, B_136, C_138), u1_struct_0(A_137)) | ~r2_lattice3(A_137, B_136, C_134) | ~m1_subset_1(C_134, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | r2_lattice3(A_135, B_136, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_135)) | ~l1_orders_2(A_135))), inference(resolution, [status(thm)], [c_28, c_285])).
% 3.22/1.53  tff(c_350, plain, (![A_135, B_136, C_138, C_134]: (r1_orders_2('#skF_5', '#skF_4'(A_135, B_136, C_138), C_134) | ~m1_subset_1('#skF_4'(A_135, B_136, C_138), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_5', B_136, C_134) | ~m1_subset_1(C_134, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | r2_lattice3(A_135, B_136, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_135)) | ~l1_orders_2(A_135))), inference(superposition, [status(thm), theory('equality')], [c_76, c_344])).
% 3.22/1.53  tff(c_429, plain, (![A_163, B_164, C_165, C_166]: (r1_orders_2('#skF_5', '#skF_4'(A_163, B_164, C_165), C_166) | ~m1_subset_1('#skF_4'(A_163, B_164, C_165), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_5', B_164, C_166) | ~m1_subset_1(C_166, u1_struct_0('#skF_6')) | r2_lattice3(A_163, B_164, C_165) | ~m1_subset_1(C_165, u1_struct_0(A_163)) | ~l1_orders_2(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_350])).
% 3.22/1.53  tff(c_434, plain, (![B_48, C_49, C_166]: (r1_orders_2('#skF_5', '#skF_4'('#skF_6', B_48, C_49), C_166) | ~r2_lattice3('#skF_5', B_48, C_166) | ~m1_subset_1(C_166, u1_struct_0('#skF_6')) | r2_lattice3('#skF_6', B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_429])).
% 3.22/1.53  tff(c_458, plain, (![B_170, C_171, C_172]: (r1_orders_2('#skF_5', '#skF_4'('#skF_6', B_170, C_171), C_172) | ~r2_lattice3('#skF_5', B_170, C_172) | ~m1_subset_1(C_172, u1_struct_0('#skF_6')) | r2_lattice3('#skF_6', B_170, C_171) | ~m1_subset_1(C_171, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_434])).
% 3.22/1.53  tff(c_91, plain, (m1_subset_1(u1_orders_2('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')))) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_76, c_6])).
% 3.22/1.53  tff(c_101, plain, (m1_subset_1(u1_orders_2('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_91])).
% 3.22/1.53  tff(c_87, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_5'))=g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36])).
% 3.22/1.53  tff(c_8, plain, (![D_14, B_10, C_13, A_9]: (D_14=B_10 | g1_orders_2(C_13, D_14)!=g1_orders_2(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.53  tff(c_114, plain, (![D_14, C_13]: (u1_orders_2('#skF_5')=D_14 | g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_87, c_8])).
% 3.22/1.53  tff(c_122, plain, (![D_14, C_13]: (u1_orders_2('#skF_5')=D_14 | g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_114])).
% 3.22/1.53  tff(c_140, plain, (u1_orders_2('#skF_5')=u1_orders_2('#skF_6')), inference(reflexivity, [status(thm), theory('equality')], [c_122])).
% 3.22/1.53  tff(c_201, plain, (![B_104, C_105, A_106]: (r2_hidden(k4_tarski(B_104, C_105), u1_orders_2(A_106)) | ~r1_orders_2(A_106, B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_106)) | ~m1_subset_1(B_104, u1_struct_0(A_106)) | ~l1_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.53  tff(c_211, plain, (![B_104, C_105]: (r2_hidden(k4_tarski(B_104, C_105), u1_orders_2('#skF_6')) | ~r1_orders_2('#skF_5', B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0('#skF_5')) | ~m1_subset_1(B_104, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_201])).
% 3.22/1.53  tff(c_254, plain, (![B_111, C_112]: (r2_hidden(k4_tarski(B_111, C_112), u1_orders_2('#skF_6')) | ~r1_orders_2('#skF_5', B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0('#skF_6')) | ~m1_subset_1(B_111, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_76, c_211])).
% 3.22/1.53  tff(c_2, plain, (![A_1, B_5, C_7]: (r1_orders_2(A_1, B_5, C_7) | ~r2_hidden(k4_tarski(B_5, C_7), u1_orders_2(A_1)) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~m1_subset_1(B_5, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.53  tff(c_260, plain, (![B_111, C_112]: (r1_orders_2('#skF_6', B_111, C_112) | ~l1_orders_2('#skF_6') | ~r1_orders_2('#skF_5', B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0('#skF_6')) | ~m1_subset_1(B_111, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_254, c_2])).
% 3.22/1.53  tff(c_264, plain, (![B_111, C_112]: (r1_orders_2('#skF_6', B_111, C_112) | ~r1_orders_2('#skF_5', B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0('#skF_6')) | ~m1_subset_1(B_111, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_260])).
% 3.22/1.53  tff(c_468, plain, (![B_173, C_174, C_175]: (r1_orders_2('#skF_6', '#skF_4'('#skF_6', B_173, C_174), C_175) | ~m1_subset_1('#skF_4'('#skF_6', B_173, C_174), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_5', B_173, C_175) | ~m1_subset_1(C_175, u1_struct_0('#skF_6')) | r2_lattice3('#skF_6', B_173, C_174) | ~m1_subset_1(C_174, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_458, c_264])).
% 3.22/1.53  tff(c_471, plain, (![B_48, C_49, C_175]: (r1_orders_2('#skF_6', '#skF_4'('#skF_6', B_48, C_49), C_175) | ~r2_lattice3('#skF_5', B_48, C_175) | ~m1_subset_1(C_175, u1_struct_0('#skF_6')) | r2_lattice3('#skF_6', B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_468])).
% 3.22/1.53  tff(c_480, plain, (![B_179, C_180, C_181]: (r1_orders_2('#skF_6', '#skF_4'('#skF_6', B_179, C_180), C_181) | ~r2_lattice3('#skF_5', B_179, C_181) | ~m1_subset_1(C_181, u1_struct_0('#skF_6')) | r2_lattice3('#skF_6', B_179, C_180) | ~m1_subset_1(C_180, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_471])).
% 3.22/1.53  tff(c_26, plain, (![A_41, B_48, C_49]: (~r1_orders_2(A_41, '#skF_4'(A_41, B_48, C_49), C_49) | r2_lattice3(A_41, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_41)) | ~l1_orders_2(A_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.53  tff(c_487, plain, (![B_179, C_181]: (~l1_orders_2('#skF_6') | ~r2_lattice3('#skF_5', B_179, C_181) | r2_lattice3('#skF_6', B_179, C_181) | ~m1_subset_1(C_181, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_480, c_26])).
% 3.22/1.53  tff(c_495, plain, (![B_182, C_183]: (~r2_lattice3('#skF_5', B_182, C_183) | r2_lattice3('#skF_6', B_182, C_183) | ~m1_subset_1(C_183, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_487])).
% 3.22/1.53  tff(c_503, plain, (![B_30]: (r2_lattice3('#skF_6', B_30, '#skF_1'('#skF_5', B_30)) | ~m1_subset_1('#skF_1'('#skF_5', B_30), u1_struct_0('#skF_6')) | ~v3_lattice3('#skF_5') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_495])).
% 3.22/1.53  tff(c_512, plain, (![B_30]: (r2_lattice3('#skF_6', B_30, '#skF_1'('#skF_5', B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_105, c_503])).
% 3.22/1.53  tff(c_14, plain, (![A_15, C_39]: (r2_lattice3(A_15, '#skF_2'(A_15), '#skF_3'(A_15, C_39)) | v3_lattice3(A_15) | ~r2_lattice3(A_15, '#skF_2'(A_15), C_39) | ~m1_subset_1(C_39, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_16, plain, (![A_15, C_39]: (m1_subset_1('#skF_3'(A_15, C_39), u1_struct_0(A_15)) | v3_lattice3(A_15) | ~r2_lattice3(A_15, '#skF_2'(A_15), C_39) | ~m1_subset_1(C_39, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_513, plain, (![B_184]: (r2_lattice3('#skF_6', B_184, '#skF_1'('#skF_5', B_184)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_105, c_503])).
% 3.22/1.53  tff(c_194, plain, (![A_99, B_100, C_101]: (r1_orders_2(A_99, B_100, C_101) | ~r2_hidden(k4_tarski(B_100, C_101), u1_orders_2(A_99)) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_orders_2(A_99))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.53  tff(c_197, plain, (![B_100, C_101]: (r1_orders_2('#skF_5', B_100, C_101) | ~r2_hidden(k4_tarski(B_100, C_101), u1_orders_2('#skF_6')) | ~m1_subset_1(C_101, u1_struct_0('#skF_5')) | ~m1_subset_1(B_100, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_194])).
% 3.22/1.53  tff(c_199, plain, (![B_100, C_101]: (r1_orders_2('#skF_5', B_100, C_101) | ~r2_hidden(k4_tarski(B_100, C_101), u1_orders_2('#skF_6')) | ~m1_subset_1(C_101, u1_struct_0('#skF_6')) | ~m1_subset_1(B_100, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_76, c_197])).
% 3.22/1.53  tff(c_205, plain, (![B_104, C_105]: (r1_orders_2('#skF_5', B_104, C_105) | ~r1_orders_2('#skF_6', B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0('#skF_6')) | ~m1_subset_1(B_104, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_201, c_199])).
% 3.22/1.53  tff(c_220, plain, (![B_107, C_108]: (r1_orders_2('#skF_5', B_107, C_108) | ~r1_orders_2('#skF_6', B_107, C_108) | ~m1_subset_1(C_108, u1_struct_0('#skF_6')) | ~m1_subset_1(B_107, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_205])).
% 3.22/1.53  tff(c_223, plain, (![B_107, C_39]: (r1_orders_2('#skF_5', B_107, '#skF_3'('#skF_6', C_39)) | ~r1_orders_2('#skF_6', B_107, '#skF_3'('#skF_6', C_39)) | ~m1_subset_1(B_107, u1_struct_0('#skF_6')) | v3_lattice3('#skF_6') | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), C_39) | ~m1_subset_1(C_39, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_16, c_220])).
% 3.22/1.53  tff(c_236, plain, (![B_107, C_39]: (r1_orders_2('#skF_5', B_107, '#skF_3'('#skF_6', C_39)) | ~r1_orders_2('#skF_6', B_107, '#skF_3'('#skF_6', C_39)) | ~m1_subset_1(B_107, u1_struct_0('#skF_6')) | v3_lattice3('#skF_6') | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), C_39) | ~m1_subset_1(C_39, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_223])).
% 3.22/1.53  tff(c_237, plain, (![B_107, C_39]: (r1_orders_2('#skF_5', B_107, '#skF_3'('#skF_6', C_39)) | ~r1_orders_2('#skF_6', B_107, '#skF_3'('#skF_6', C_39)) | ~m1_subset_1(B_107, u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), C_39) | ~m1_subset_1(C_39, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_236])).
% 3.22/1.53  tff(c_516, plain, (![B_107]: (r1_orders_2('#skF_5', B_107, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~r1_orders_2('#skF_6', B_107, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1(B_107, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_2'('#skF_6')), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_513, c_237])).
% 3.22/1.53  tff(c_528, plain, (![B_186]: (r1_orders_2('#skF_5', B_186, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~r1_orders_2('#skF_6', B_186, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1(B_186, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_516])).
% 3.22/1.53  tff(c_534, plain, (![B_48]: (r2_lattice3('#skF_5', B_48, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r1_orders_2('#skF_6', '#skF_4'('#skF_5', B_48, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_4'('#skF_5', B_48, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_528, c_26])).
% 3.22/1.53  tff(c_538, plain, (![B_48]: (r2_lattice3('#skF_5', B_48, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_6')) | ~r1_orders_2('#skF_6', '#skF_4'('#skF_5', B_48, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_4'('#skF_5', B_48, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_534])).
% 3.22/1.53  tff(c_632, plain, (~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_538])).
% 3.22/1.53  tff(c_641, plain, (v3_lattice3('#skF_6') | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_1'('#skF_5', '#skF_2'('#skF_6'))) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_2'('#skF_6')), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_16, c_632])).
% 3.22/1.53  tff(c_644, plain, (v3_lattice3('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_105, c_512, c_641])).
% 3.22/1.53  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_644])).
% 3.22/1.53  tff(c_648, plain, (m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_538])).
% 3.22/1.53  tff(c_165, plain, (![A_83, B_84, C_85]: (m1_subset_1('#skF_4'(A_83, B_84, C_85), u1_struct_0(A_83)) | r2_lattice3(A_83, B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0(A_83)) | ~l1_orders_2(A_83))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.53  tff(c_168, plain, (![B_84, C_85]: (m1_subset_1('#skF_4'('#skF_5', B_84, C_85), u1_struct_0('#skF_6')) | r2_lattice3('#skF_5', B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_165])).
% 3.22/1.53  tff(c_170, plain, (![B_84, C_85]: (m1_subset_1('#skF_4'('#skF_5', B_84, C_85), u1_struct_0('#skF_6')) | r2_lattice3('#skF_5', B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_168])).
% 3.22/1.53  tff(c_346, plain, (![B_84, C_85, C_134]: (r1_orders_2('#skF_6', '#skF_4'('#skF_5', B_84, C_85), C_134) | ~r2_lattice3('#skF_6', B_84, C_134) | ~m1_subset_1(C_134, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~m1_subset_1(C_85, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | r2_lattice3('#skF_5', B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_170, c_344])).
% 3.22/1.53  tff(c_353, plain, (![B_84, C_85, C_134]: (r1_orders_2('#skF_6', '#skF_4'('#skF_5', B_84, C_85), C_134) | ~r2_lattice3('#skF_6', B_84, C_134) | ~m1_subset_1(C_134, u1_struct_0('#skF_6')) | r2_lattice3('#skF_5', B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76, c_38, c_346])).
% 3.22/1.53  tff(c_652, plain, (![B_235]: (r2_lattice3('#skF_5', B_235, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~r1_orders_2('#skF_6', '#skF_4'('#skF_5', B_235, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_4'('#skF_5', B_235, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_538])).
% 3.22/1.53  tff(c_660, plain, (![B_84]: (~m1_subset_1('#skF_4'('#skF_5', B_84, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_6', B_84, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | r2_lattice3('#skF_5', B_84, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_353, c_652])).
% 3.22/1.53  tff(c_667, plain, (![B_236]: (~m1_subset_1('#skF_4'('#skF_5', B_236, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_6', B_236, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | r2_lattice3('#skF_5', B_236, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_660])).
% 3.22/1.53  tff(c_671, plain, (![B_84]: (~r2_lattice3('#skF_6', B_84, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | r2_lattice3('#skF_5', B_84, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_170, c_667])).
% 3.22/1.53  tff(c_675, plain, (![B_237]: (~r2_lattice3('#skF_6', B_237, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))) | r2_lattice3('#skF_5', B_237, '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6')))))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_671])).
% 3.22/1.53  tff(c_18, plain, (![A_15, B_30, D_35]: (r1_orders_2(A_15, '#skF_1'(A_15, B_30), D_35) | ~r2_lattice3(A_15, B_30, D_35) | ~m1_subset_1(D_35, u1_struct_0(A_15)) | ~v3_lattice3(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_265, plain, (![B_113, C_114]: (r1_orders_2('#skF_6', B_113, C_114) | ~r1_orders_2('#skF_5', B_113, C_114) | ~m1_subset_1(C_114, u1_struct_0('#skF_6')) | ~m1_subset_1(B_113, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_260])).
% 3.22/1.53  tff(c_270, plain, (![B_30, D_35]: (r1_orders_2('#skF_6', '#skF_1'('#skF_5', B_30), D_35) | ~m1_subset_1(D_35, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_5', B_30), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_5', B_30, D_35) | ~m1_subset_1(D_35, u1_struct_0('#skF_5')) | ~v3_lattice3('#skF_5') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_265])).
% 3.22/1.53  tff(c_277, plain, (![B_115, D_116]: (r1_orders_2('#skF_6', '#skF_1'('#skF_5', B_115), D_116) | ~r2_lattice3('#skF_5', B_115, D_116) | ~m1_subset_1(D_116, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_76, c_105, c_270])).
% 3.22/1.53  tff(c_12, plain, (![A_15, C_39]: (~r1_orders_2(A_15, C_39, '#skF_3'(A_15, C_39)) | v3_lattice3(A_15) | ~r2_lattice3(A_15, '#skF_2'(A_15), C_39) | ~m1_subset_1(C_39, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.53  tff(c_280, plain, (![B_115]: (v3_lattice3('#skF_6') | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_1'('#skF_5', B_115)) | ~m1_subset_1('#skF_1'('#skF_5', B_115), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~r2_lattice3('#skF_5', B_115, '#skF_3'('#skF_6', '#skF_1'('#skF_5', B_115))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', B_115)), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_277, c_12])).
% 3.22/1.53  tff(c_283, plain, (![B_115]: (v3_lattice3('#skF_6') | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_1'('#skF_5', B_115)) | ~r2_lattice3('#skF_5', B_115, '#skF_3'('#skF_6', '#skF_1'('#skF_5', B_115))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', B_115)), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_105, c_280])).
% 3.22/1.53  tff(c_284, plain, (![B_115]: (~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_1'('#skF_5', B_115)) | ~r2_lattice3('#skF_5', B_115, '#skF_3'('#skF_6', '#skF_1'('#skF_5', B_115))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', B_115)), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_283])).
% 3.22/1.53  tff(c_680, plain, (~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_1'('#skF_5', '#skF_2'('#skF_6'))) | ~m1_subset_1('#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))))), inference(resolution, [status(thm)], [c_675, c_284])).
% 3.22/1.53  tff(c_686, plain, (~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_3'('#skF_6', '#skF_1'('#skF_5', '#skF_2'('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_512, c_680])).
% 3.22/1.53  tff(c_695, plain, (v3_lattice3('#skF_6') | ~r2_lattice3('#skF_6', '#skF_2'('#skF_6'), '#skF_1'('#skF_5', '#skF_2'('#skF_6'))) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_2'('#skF_6')), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_14, c_686])).
% 3.22/1.53  tff(c_698, plain, (v3_lattice3('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_105, c_512, c_695])).
% 3.22/1.53  tff(c_700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_698])).
% 3.22/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.53  
% 3.22/1.53  Inference rules
% 3.22/1.53  ----------------------
% 3.22/1.53  #Ref     : 6
% 3.22/1.53  #Sup     : 112
% 3.22/1.53  #Fact    : 0
% 3.22/1.53  #Define  : 0
% 3.22/1.53  #Split   : 1
% 3.22/1.53  #Chain   : 0
% 3.22/1.53  #Close   : 0
% 3.22/1.53  
% 3.22/1.53  Ordering : KBO
% 3.22/1.53  
% 3.22/1.53  Simplification rules
% 3.22/1.53  ----------------------
% 3.22/1.53  #Subsume      : 22
% 3.22/1.53  #Demod        : 132
% 3.22/1.53  #Tautology    : 43
% 3.22/1.53  #SimpNegUnit  : 10
% 3.22/1.53  #BackRed      : 5
% 3.22/1.53  
% 3.22/1.53  #Partial instantiations: 0
% 3.22/1.53  #Strategies tried      : 1
% 3.22/1.53  
% 3.22/1.53  Timing (in seconds)
% 3.22/1.53  ----------------------
% 3.22/1.53  Preprocessing        : 0.30
% 3.22/1.53  Parsing              : 0.16
% 3.22/1.53  CNF conversion       : 0.03
% 3.22/1.53  Main loop            : 0.41
% 3.22/1.53  Inferencing          : 0.17
% 3.22/1.53  Reduction            : 0.12
% 3.22/1.53  Demodulation         : 0.08
% 3.22/1.53  BG Simplification    : 0.02
% 3.22/1.53  Subsumption          : 0.08
% 3.22/1.53  Abstraction          : 0.02
% 3.22/1.53  MUC search           : 0.00
% 3.22/1.53  Cooper               : 0.00
% 3.22/1.53  Total                : 0.76
% 3.22/1.53  Index Insertion      : 0.00
% 3.22/1.53  Index Deletion       : 0.00
% 3.22/1.53  Index Matching       : 0.00
% 3.22/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
