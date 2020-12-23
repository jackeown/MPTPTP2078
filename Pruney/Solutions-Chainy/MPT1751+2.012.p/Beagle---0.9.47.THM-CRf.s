%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:59 EST 2020

% Result     : Theorem 17.64s
% Output     : CNFRefutation 17.64s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 258 expanded)
%              Number of leaves         :   37 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 (1242 expanded)
%              Number of equality atoms :   31 ( 129 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_26,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_67,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_266,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k2_partfun1(A_122,B_123,C_124,D_125) = k7_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_268,plain,(
    ! [D_125] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_125) = k7_relat_1('#skF_4',D_125)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_266])).

tff(c_274,plain,(
    ! [D_125] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_125) = k7_relat_1('#skF_4',D_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_268])).

tff(c_602,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k2_partfun1(u1_struct_0(A_166),u1_struct_0(B_167),C_168,u1_struct_0(D_169)) = k2_tmap_1(A_166,B_167,C_168,D_169)
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_pre_topc(B_167)
      | ~ v2_pre_topc(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_607,plain,(
    ! [D_169] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_169)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_169)
      | ~ m1_pre_topc(D_169,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_602])).

tff(c_617,plain,(
    ! [D_169] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_169)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_169)
      | ~ m1_pre_topc(D_169,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_48,c_46,c_34,c_32,c_274,c_607])).

tff(c_622,plain,(
    ! [D_170] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_170)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_170)
      | ~ m1_pre_topc(D_170,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_617])).

tff(c_8,plain,(
    ! [A_6,C_10,B_9] :
      ( k9_relat_1(k7_relat_1(A_6,C_10),B_9) = k9_relat_1(A_6,B_9)
      | ~ r1_tarski(B_9,C_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_661,plain,(
    ! [D_170,B_9] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_170),B_9) = k9_relat_1('#skF_4',B_9)
      | ~ r1_tarski(B_9,u1_struct_0(D_170))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_170,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_8])).

tff(c_1317,plain,(
    ! [D_235,B_236] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_235),B_236) = k9_relat_1('#skF_4',B_236)
      | ~ r1_tarski(B_236,u1_struct_0(D_235))
      | ~ m1_pre_topc(D_235,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_661])).

tff(c_1368,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1317])).

tff(c_1391,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1368])).

tff(c_618,plain,(
    ! [D_169] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_169)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_169)
      | ~ m1_pre_topc(D_169,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_617])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_4])).

tff(c_93,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,C_86)
      | ~ r1_tarski(B_87,C_86)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_85] :
      ( r1_tarski(A_85,k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_85,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_93])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_429,plain,(
    ! [D_148,B_149,C_150,A_151] :
      ( m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(B_149,C_150)))
      | ~ r1_tarski(k1_relat_1(D_148),B_149)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_151,C_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_834,plain,(
    ! [A_190,B_191,C_192,A_193] :
      ( m1_subset_1(A_190,k1_zfmisc_1(k2_zfmisc_1(B_191,C_192)))
      | ~ r1_tarski(k1_relat_1(A_190),B_191)
      | ~ r1_tarski(A_190,k2_zfmisc_1(A_193,C_192)) ) ),
    inference(resolution,[status(thm)],[c_6,c_429])).

tff(c_870,plain,(
    ! [A_195,B_196] :
      ( m1_subset_1(A_195,k1_zfmisc_1(k2_zfmisc_1(B_196,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1(A_195),B_196)
      | ~ r1_tarski(A_195,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105,c_834])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k7_relset_1(A_18,B_19,C_20,D_21) = k9_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1857,plain,(
    ! [B_284,A_285,D_286] :
      ( k7_relset_1(B_284,u1_struct_0('#skF_1'),A_285,D_286) = k9_relat_1(A_285,D_286)
      | ~ r1_tarski(k1_relat_1(A_285),B_284)
      | ~ r1_tarski(A_285,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_870,c_16])).

tff(c_6749,plain,(
    ! [A_641,B_642,D_643] :
      ( k7_relset_1(A_641,u1_struct_0('#skF_1'),k7_relat_1(B_642,A_641),D_643) = k9_relat_1(k7_relat_1(B_642,A_641),D_643)
      | ~ r1_tarski(k7_relat_1(B_642,A_641),'#skF_4')
      | ~ v1_relat_1(B_642) ) ),
    inference(resolution,[status(thm)],[c_10,c_1857])).

tff(c_6802,plain,(
    ! [D_169,D_643] :
      ( k7_relset_1(u1_struct_0(D_169),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_169),D_643) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_169)),D_643)
      | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0(D_169)),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_169,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_6749])).

tff(c_30246,plain,(
    ! [D_2056,D_2057] :
      ( k7_relset_1(u1_struct_0(D_2056),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_2056),D_2057) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_2056)),D_2057)
      | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0(D_2056)),'#skF_4')
      | ~ m1_pre_topc(D_2056,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_6802])).

tff(c_189,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k7_relset_1(A_108,B_109,C_110,D_111) = k9_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,(
    ! [D_111] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_111) = k9_relat_1('#skF_4',D_111) ),
    inference(resolution,[status(thm)],[c_30,c_189])).

tff(c_24,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_197,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_24])).

tff(c_30260,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30246,c_197])).

tff(c_30276,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30260])).

tff(c_30280,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30276])).

tff(c_30286,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_30280])).

tff(c_30292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_30286])).

tff(c_30293,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30276])).

tff(c_30375,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_30293])).

tff(c_30381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1391,c_30375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.64/9.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.64/9.36  
% 17.64/9.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.64/9.36  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 17.64/9.36  
% 17.64/9.36  %Foreground sorts:
% 17.64/9.36  
% 17.64/9.36  
% 17.64/9.36  %Background operators:
% 17.64/9.36  
% 17.64/9.36  
% 17.64/9.36  %Foreground operators:
% 17.64/9.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 17.64/9.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.64/9.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.64/9.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 17.64/9.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.64/9.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.64/9.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 17.64/9.36  tff('#skF_5', type, '#skF_5': $i).
% 17.64/9.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.64/9.36  tff('#skF_2', type, '#skF_2': $i).
% 17.64/9.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 17.64/9.36  tff('#skF_3', type, '#skF_3': $i).
% 17.64/9.36  tff('#skF_1', type, '#skF_1': $i).
% 17.64/9.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.64/9.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.64/9.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.64/9.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.64/9.36  tff('#skF_4', type, '#skF_4': $i).
% 17.64/9.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.64/9.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 17.64/9.36  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 17.64/9.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.64/9.36  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 17.64/9.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.64/9.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.64/9.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.64/9.36  
% 17.64/9.37  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 17.64/9.37  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.64/9.37  tff(f_70, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 17.64/9.37  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 17.64/9.37  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 17.64/9.37  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 17.64/9.37  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 17.64/9.37  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 17.64/9.37  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 17.64/9.37  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 17.64/9.37  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 17.64/9.37  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_26, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_67, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.64/9.37  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_67])).
% 17.64/9.37  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_266, plain, (![A_122, B_123, C_124, D_125]: (k2_partfun1(A_122, B_123, C_124, D_125)=k7_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.64/9.37  tff(c_268, plain, (![D_125]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_125)=k7_relat_1('#skF_4', D_125) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_266])).
% 17.64/9.37  tff(c_274, plain, (![D_125]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_125)=k7_relat_1('#skF_4', D_125))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_268])).
% 17.64/9.37  tff(c_602, plain, (![A_166, B_167, C_168, D_169]: (k2_partfun1(u1_struct_0(A_166), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1(A_166, B_167, C_168, D_169) | ~m1_pre_topc(D_169, A_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.64/9.37  tff(c_607, plain, (![D_169]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_169))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_169) | ~m1_pre_topc(D_169, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_602])).
% 17.64/9.37  tff(c_617, plain, (![D_169]: (k7_relat_1('#skF_4', u1_struct_0(D_169))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_169) | ~m1_pre_topc(D_169, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_48, c_46, c_34, c_32, c_274, c_607])).
% 17.64/9.37  tff(c_622, plain, (![D_170]: (k7_relat_1('#skF_4', u1_struct_0(D_170))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_170) | ~m1_pre_topc(D_170, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_617])).
% 17.64/9.37  tff(c_8, plain, (![A_6, C_10, B_9]: (k9_relat_1(k7_relat_1(A_6, C_10), B_9)=k9_relat_1(A_6, B_9) | ~r1_tarski(B_9, C_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.64/9.37  tff(c_661, plain, (![D_170, B_9]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_170), B_9)=k9_relat_1('#skF_4', B_9) | ~r1_tarski(B_9, u1_struct_0(D_170)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_170, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_622, c_8])).
% 17.64/9.37  tff(c_1317, plain, (![D_235, B_236]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_235), B_236)=k9_relat_1('#skF_4', B_236) | ~r1_tarski(B_236, u1_struct_0(D_235)) | ~m1_pre_topc(D_235, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_661])).
% 17.64/9.37  tff(c_1368, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_1317])).
% 17.64/9.37  tff(c_1391, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1368])).
% 17.64/9.37  tff(c_618, plain, (![D_169]: (k7_relat_1('#skF_4', u1_struct_0(D_169))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_169) | ~m1_pre_topc(D_169, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_617])).
% 17.64/9.37  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.64/9.37  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.64/9.37  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.64/9.37  tff(c_65, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_4])).
% 17.64/9.37  tff(c_93, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, C_86) | ~r1_tarski(B_87, C_86) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.64/9.37  tff(c_105, plain, (![A_85]: (r1_tarski(A_85, k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))) | ~r1_tarski(A_85, '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_93])).
% 17.64/9.37  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.64/9.37  tff(c_429, plain, (![D_148, B_149, C_150, A_151]: (m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(B_149, C_150))) | ~r1_tarski(k1_relat_1(D_148), B_149) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_151, C_150))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.64/9.37  tff(c_834, plain, (![A_190, B_191, C_192, A_193]: (m1_subset_1(A_190, k1_zfmisc_1(k2_zfmisc_1(B_191, C_192))) | ~r1_tarski(k1_relat_1(A_190), B_191) | ~r1_tarski(A_190, k2_zfmisc_1(A_193, C_192)))), inference(resolution, [status(thm)], [c_6, c_429])).
% 17.64/9.37  tff(c_870, plain, (![A_195, B_196]: (m1_subset_1(A_195, k1_zfmisc_1(k2_zfmisc_1(B_196, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1(A_195), B_196) | ~r1_tarski(A_195, '#skF_4'))), inference(resolution, [status(thm)], [c_105, c_834])).
% 17.64/9.37  tff(c_16, plain, (![A_18, B_19, C_20, D_21]: (k7_relset_1(A_18, B_19, C_20, D_21)=k9_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.64/9.37  tff(c_1857, plain, (![B_284, A_285, D_286]: (k7_relset_1(B_284, u1_struct_0('#skF_1'), A_285, D_286)=k9_relat_1(A_285, D_286) | ~r1_tarski(k1_relat_1(A_285), B_284) | ~r1_tarski(A_285, '#skF_4'))), inference(resolution, [status(thm)], [c_870, c_16])).
% 17.64/9.37  tff(c_6749, plain, (![A_641, B_642, D_643]: (k7_relset_1(A_641, u1_struct_0('#skF_1'), k7_relat_1(B_642, A_641), D_643)=k9_relat_1(k7_relat_1(B_642, A_641), D_643) | ~r1_tarski(k7_relat_1(B_642, A_641), '#skF_4') | ~v1_relat_1(B_642))), inference(resolution, [status(thm)], [c_10, c_1857])).
% 17.64/9.37  tff(c_6802, plain, (![D_169, D_643]: (k7_relset_1(u1_struct_0(D_169), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_169), D_643)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_169)), D_643) | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0(D_169)), '#skF_4') | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_169, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_618, c_6749])).
% 17.64/9.37  tff(c_30246, plain, (![D_2056, D_2057]: (k7_relset_1(u1_struct_0(D_2056), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_2056), D_2057)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_2056)), D_2057) | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0(D_2056)), '#skF_4') | ~m1_pre_topc(D_2056, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_6802])).
% 17.64/9.37  tff(c_189, plain, (![A_108, B_109, C_110, D_111]: (k7_relset_1(A_108, B_109, C_110, D_111)=k9_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.64/9.37  tff(c_195, plain, (![D_111]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_111)=k9_relat_1('#skF_4', D_111))), inference(resolution, [status(thm)], [c_30, c_189])).
% 17.64/9.37  tff(c_24, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 17.64/9.37  tff(c_197, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_24])).
% 17.64/9.37  tff(c_30260, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30246, c_197])).
% 17.64/9.37  tff(c_30276, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30260])).
% 17.64/9.37  tff(c_30280, plain, (~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_30276])).
% 17.64/9.37  tff(c_30286, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_30280])).
% 17.64/9.37  tff(c_30292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_30286])).
% 17.64/9.37  tff(c_30293, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30276])).
% 17.64/9.37  tff(c_30375, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_618, c_30293])).
% 17.64/9.37  tff(c_30381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1391, c_30375])).
% 17.64/9.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.64/9.37  
% 17.64/9.37  Inference rules
% 17.64/9.37  ----------------------
% 17.64/9.37  #Ref     : 0
% 17.64/9.37  #Sup     : 6755
% 17.64/9.37  #Fact    : 0
% 17.64/9.37  #Define  : 0
% 17.64/9.37  #Split   : 19
% 17.64/9.37  #Chain   : 0
% 17.64/9.37  #Close   : 0
% 17.64/9.37  
% 17.64/9.37  Ordering : KBO
% 17.64/9.37  
% 17.64/9.37  Simplification rules
% 17.64/9.37  ----------------------
% 17.64/9.37  #Subsume      : 1439
% 17.64/9.37  #Demod        : 1818
% 17.64/9.37  #Tautology    : 1091
% 17.64/9.37  #SimpNegUnit  : 601
% 17.64/9.37  #BackRed      : 1
% 17.64/9.37  
% 17.64/9.37  #Partial instantiations: 0
% 17.64/9.37  #Strategies tried      : 1
% 17.64/9.37  
% 17.64/9.37  Timing (in seconds)
% 17.64/9.37  ----------------------
% 17.64/9.38  Preprocessing        : 0.34
% 17.64/9.38  Parsing              : 0.18
% 17.64/9.38  CNF conversion       : 0.03
% 17.64/9.38  Main loop            : 8.26
% 17.64/9.38  Inferencing          : 2.14
% 17.64/9.38  Reduction            : 1.77
% 17.64/9.38  Demodulation         : 1.14
% 17.64/9.38  BG Simplification    : 0.18
% 17.64/9.38  Subsumption          : 3.72
% 17.64/9.38  Abstraction          : 0.36
% 17.64/9.38  MUC search           : 0.00
% 17.64/9.38  Cooper               : 0.00
% 17.64/9.38  Total                : 8.64
% 17.64/9.38  Index Insertion      : 0.00
% 17.64/9.38  Index Deletion       : 0.00
% 17.64/9.38  Index Matching       : 0.00
% 17.64/9.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
