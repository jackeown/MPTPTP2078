%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1525+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:59 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   87 (1596 expanded)
%              Number of leaves         :   26 ( 525 expanded)
%              Depth                    :   23
%              Number of atoms          :  276 (4617 expanded)
%              Number of equality atoms :   38 (1562 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > m1_subset_1 > v3_lattice3 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C,D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ! [E] :
                    ( m1_subset_1(E,u1_struct_0(B))
                   => ( D = E
                     => ( ( r2_lattice3(A,C,D)
                         => r2_lattice3(B,C,E) )
                        & ( r1_lattice3(A,C,D)
                         => r1_lattice3(B,C,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( C = E
                                & D = F )
                             => ( ( r1_orders_2(A,C,D)
                                 => r1_orders_2(B,E,F) )
                                & ( r2_orders_2(A,C,D)
                                 => r2_orders_2(B,E,F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    v3_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12,plain,(
    ! [A_1,B_16] :
      ( m1_subset_1('#skF_1'(A_1,B_16),u1_struct_0(A_1))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14,plain,(
    ! [A_27] :
      ( m1_subset_1(u1_orders_2(A_27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_27),u1_struct_0(A_27))))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    ! [D_122,B_123,C_124,A_125] :
      ( D_122 = B_123
      | g1_orders_2(C_124,D_122) != g1_orders_2(A_125,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_zfmisc_1(A_125,A_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ! [B_126,A_127] :
      ( u1_orders_2('#skF_5') = B_126
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_127,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(A_127,A_127))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_48])).

tff(c_57,plain,(
    ! [A_27] :
      ( u1_orders_2(A_27) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_27),u1_orders_2(A_27)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_27) ) ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_69,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_57])).

tff(c_71,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_69])).

tff(c_86,plain,
    ( m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_14])).

tff(c_90,plain,(
    m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_86])).

tff(c_82,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_4')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_32])).

tff(c_18,plain,(
    ! [C_32,A_28,D_33,B_29] :
      ( C_32 = A_28
      | g1_orders_2(C_32,D_33) != g1_orders_2(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,(
    ! [C_32,D_33] :
      ( u1_struct_0('#skF_5') = C_32
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_32,D_33)
      | ~ m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_18])).

tff(c_104,plain,(
    ! [C_32,D_33] :
      ( u1_struct_0('#skF_5') = C_32
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_32,D_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_96])).

tff(c_111,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_104])).

tff(c_10,plain,(
    ! [A_1,B_16] :
      ( r2_lattice3(A_1,B_16,'#skF_1'(A_1,B_16))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [B_149,C_150,E_151,A_152] :
      ( r2_lattice3(B_149,C_150,E_151)
      | ~ r2_lattice3(A_152,C_150,E_151)
      | ~ m1_subset_1(E_151,u1_struct_0(B_149))
      | ~ m1_subset_1(E_151,u1_struct_0(A_152))
      | g1_orders_2(u1_struct_0(B_149),u1_orders_2(B_149)) != g1_orders_2(u1_struct_0(A_152),u1_orders_2(A_152))
      | ~ l1_orders_2(B_149)
      | ~ l1_orders_2(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_180,plain,(
    ! [B_157,B_158,A_159] :
      ( r2_lattice3(B_157,B_158,'#skF_1'(A_159,B_158))
      | ~ m1_subset_1('#skF_1'(A_159,B_158),u1_struct_0(B_157))
      | ~ m1_subset_1('#skF_1'(A_159,B_158),u1_struct_0(A_159))
      | g1_orders_2(u1_struct_0(B_157),u1_orders_2(B_157)) != g1_orders_2(u1_struct_0(A_159),u1_orders_2(A_159))
      | ~ l1_orders_2(B_157)
      | ~ v3_lattice3(A_159)
      | ~ l1_orders_2(A_159) ) ),
    inference(resolution,[status(thm)],[c_10,c_172])).

tff(c_182,plain,(
    ! [B_158,A_159] :
      ( r2_lattice3('#skF_5',B_158,'#skF_1'(A_159,B_158))
      | ~ m1_subset_1('#skF_1'(A_159,B_158),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_159,B_158),u1_struct_0(A_159))
      | g1_orders_2(u1_struct_0(A_159),u1_orders_2(A_159)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_lattice3(A_159)
      | ~ l1_orders_2(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_180])).

tff(c_192,plain,(
    ! [B_164,A_165] :
      ( r2_lattice3('#skF_5',B_164,'#skF_1'(A_165,B_164))
      | ~ m1_subset_1('#skF_1'(A_165,B_164),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_165,B_164),u1_struct_0(A_165))
      | g1_orders_2(u1_struct_0(A_165),u1_orders_2(A_165)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ v3_lattice3(A_165)
      | ~ l1_orders_2(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_111,c_71,c_182])).

tff(c_195,plain,(
    ! [B_16] :
      ( r2_lattice3('#skF_5',B_16,'#skF_1'('#skF_4',B_16))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_16),u1_struct_0('#skF_4'))
      | ~ v3_lattice3('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_199,plain,(
    ! [B_166] :
      ( r2_lattice3('#skF_5',B_166,'#skF_1'('#skF_4',B_166))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_166),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_195])).

tff(c_202,plain,(
    ! [B_16] :
      ( r2_lattice3('#skF_5',B_16,'#skF_1'('#skF_4',B_16))
      | ~ v3_lattice3('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_199])).

tff(c_205,plain,(
    ! [B_16] : r2_lattice3('#skF_5',B_16,'#skF_1'('#skF_4',B_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_202])).

tff(c_28,plain,(
    ~ v3_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4,plain,(
    ! [A_1,C_25] :
      ( r2_lattice3(A_1,'#skF_2'(A_1),'#skF_3'(A_1,C_25))
      | v3_lattice3(A_1)
      | ~ r2_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [B_176,A_177,C_178] :
      ( r2_lattice3(B_176,'#skF_2'(A_177),'#skF_3'(A_177,C_178))
      | ~ m1_subset_1('#skF_3'(A_177,C_178),u1_struct_0(B_176))
      | ~ m1_subset_1('#skF_3'(A_177,C_178),u1_struct_0(A_177))
      | g1_orders_2(u1_struct_0(B_176),u1_orders_2(B_176)) != g1_orders_2(u1_struct_0(A_177),u1_orders_2(A_177))
      | ~ l1_orders_2(B_176)
      | v3_lattice3(A_177)
      | ~ r2_lattice3(A_177,'#skF_2'(A_177),C_178)
      | ~ m1_subset_1(C_178,u1_struct_0(A_177))
      | ~ l1_orders_2(A_177) ) ),
    inference(resolution,[status(thm)],[c_4,c_172])).

tff(c_250,plain,(
    ! [B_176,C_178] :
      ( r2_lattice3(B_176,'#skF_2'('#skF_5'),'#skF_3'('#skF_5',C_178))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0(B_176))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0('#skF_5'))
      | g1_orders_2(u1_struct_0(B_176),u1_orders_2(B_176)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_176)
      | v3_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_242])).

tff(c_259,plain,(
    ! [B_176,C_178] :
      ( r2_lattice3(B_176,'#skF_2'('#skF_5'),'#skF_3'('#skF_5',C_178))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0(B_176))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_176),u1_orders_2(B_176)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_176)
      | v3_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_111,c_111,c_111,c_250])).

tff(c_260,plain,(
    ! [B_176,C_178] :
      ( r2_lattice3(B_176,'#skF_2'('#skF_5'),'#skF_3'('#skF_5',C_178))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0(B_176))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_176),u1_orders_2(B_176)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_176)
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_259])).

tff(c_263,plain,(
    ! [C_178] :
      ( r2_lattice3('#skF_4','#skF_2'('#skF_5'),'#skF_3'('#skF_5',C_178))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_4')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_260])).

tff(c_265,plain,(
    ! [C_178] :
      ( r2_lattice3('#skF_4','#skF_2'('#skF_5'),'#skF_3'('#skF_5',C_178))
      | ~ m1_subset_1('#skF_3'('#skF_5',C_178),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_263])).

tff(c_8,plain,(
    ! [A_1,B_16,D_21] :
      ( r1_orders_2(A_1,'#skF_1'(A_1,B_16),D_21)
      | ~ r2_lattice3(A_1,B_16,D_21)
      | ~ m1_subset_1(D_21,u1_struct_0(A_1))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [B_160,E_161,F_162,A_163] :
      ( r1_orders_2(B_160,E_161,F_162)
      | ~ r1_orders_2(A_163,E_161,F_162)
      | ~ m1_subset_1(F_162,u1_struct_0(B_160))
      | ~ m1_subset_1(E_161,u1_struct_0(B_160))
      | ~ m1_subset_1(F_162,u1_struct_0(A_163))
      | ~ m1_subset_1(E_161,u1_struct_0(A_163))
      | g1_orders_2(u1_struct_0(B_160),u1_orders_2(B_160)) != g1_orders_2(u1_struct_0(A_163),u1_orders_2(A_163))
      | ~ l1_orders_2(B_160)
      | ~ l1_orders_2(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_275,plain,(
    ! [B_181,A_182,B_183,D_184] :
      ( r1_orders_2(B_181,'#skF_1'(A_182,B_183),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(B_181))
      | ~ m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0(B_181))
      | ~ m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0(A_182))
      | g1_orders_2(u1_struct_0(B_181),u1_orders_2(B_181)) != g1_orders_2(u1_struct_0(A_182),u1_orders_2(A_182))
      | ~ l1_orders_2(B_181)
      | ~ r2_lattice3(A_182,B_183,D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(A_182))
      | ~ v3_lattice3(A_182)
      | ~ l1_orders_2(A_182) ) ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_277,plain,(
    ! [A_182,B_183,D_184] :
      ( r1_orders_2('#skF_5','#skF_1'(A_182,B_183),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0(A_182))
      | g1_orders_2(u1_struct_0(A_182),u1_orders_2(A_182)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3(A_182,B_183,D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(A_182))
      | ~ v3_lattice3(A_182)
      | ~ l1_orders_2(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_275])).

tff(c_301,plain,(
    ! [A_189,B_190,D_191] :
      ( r1_orders_2('#skF_5','#skF_1'(A_189,B_190),D_191)
      | ~ m1_subset_1(D_191,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_189,B_190),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_189,B_190),u1_struct_0(A_189))
      | g1_orders_2(u1_struct_0(A_189),u1_orders_2(A_189)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ r2_lattice3(A_189,B_190,D_191)
      | ~ m1_subset_1(D_191,u1_struct_0(A_189))
      | ~ v3_lattice3(A_189)
      | ~ l1_orders_2(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_111,c_71,c_111,c_277])).

tff(c_304,plain,(
    ! [B_16,D_191] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_4',B_16),D_191)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_16),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_4',B_16,D_191)
      | ~ m1_subset_1(D_191,u1_struct_0('#skF_4'))
      | ~ v3_lattice3('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_301])).

tff(c_308,plain,(
    ! [B_192,D_193] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_4',B_192),D_193)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_192),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_4',B_192,D_193)
      | ~ m1_subset_1(D_193,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_304])).

tff(c_311,plain,(
    ! [B_16,D_193] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_4',B_16),D_193)
      | ~ r2_lattice3('#skF_4',B_16,D_193)
      | ~ m1_subset_1(D_193,u1_struct_0('#skF_4'))
      | ~ v3_lattice3('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_308])).

tff(c_315,plain,(
    ! [B_194,D_195] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_4',B_194),D_195)
      | ~ r2_lattice3('#skF_4',B_194,D_195)
      | ~ m1_subset_1(D_195,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_311])).

tff(c_2,plain,(
    ! [A_1,C_25] :
      ( ~ r1_orders_2(A_1,C_25,'#skF_3'(A_1,C_25))
      | v3_lattice3(A_1)
      | ~ r2_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_320,plain,(
    ! [B_194] :
      ( v3_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),'#skF_1'('#skF_4',B_194))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_194),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_4',B_194,'#skF_3'('#skF_5','#skF_1'('#skF_4',B_194)))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_1'('#skF_4',B_194)),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_315,c_2])).

tff(c_326,plain,(
    ! [B_194] :
      ( v3_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),'#skF_1'('#skF_4',B_194))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_194),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_4',B_194,'#skF_3'('#skF_5','#skF_1'('#skF_4',B_194)))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_1'('#skF_4',B_194)),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_111,c_320])).

tff(c_342,plain,(
    ! [B_199] :
      ( ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),'#skF_1'('#skF_4',B_199))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_199),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_4',B_199,'#skF_3'('#skF_5','#skF_1'('#skF_4',B_199)))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_1'('#skF_4',B_199)),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_326])).

tff(c_345,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5','#skF_1'('#skF_4','#skF_2'('#skF_5'))),u1_struct_0('#skF_4'))
    | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),'#skF_1'('#skF_4','#skF_2'('#skF_5')))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_2'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_265,c_342])).

tff(c_348,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5','#skF_1'('#skF_4','#skF_2'('#skF_5'))),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_2'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_345])).

tff(c_349,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_2'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_352,plain,
    ( ~ v3_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_352])).

tff(c_358,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_2'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_159,plain,(
    ! [A_144,C_145] :
      ( m1_subset_1('#skF_3'(A_144,C_145),u1_struct_0(A_144))
      | v3_lattice3(A_144)
      | ~ r2_lattice3(A_144,'#skF_2'(A_144),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [C_145] :
      ( m1_subset_1('#skF_3'('#skF_5',C_145),u1_struct_0('#skF_4'))
      | v3_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_159])).

tff(c_164,plain,(
    ! [C_145] :
      ( m1_subset_1('#skF_3'('#skF_5',C_145),u1_struct_0('#skF_4'))
      | v3_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_111,c_162])).

tff(c_165,plain,(
    ! [C_145] :
      ( m1_subset_1('#skF_3'('#skF_5',C_145),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_164])).

tff(c_357,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_1'('#skF_4','#skF_2'('#skF_5'))),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_386,plain,
    ( ~ r2_lattice3('#skF_5','#skF_2'('#skF_5'),'#skF_1'('#skF_4','#skF_2'('#skF_5')))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_2'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_165,c_357])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_205,c_386])).

%------------------------------------------------------------------------------
