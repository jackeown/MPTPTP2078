%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:59 EST 2020

% Result     : Theorem 30.46s
% Output     : CNFRefutation 30.75s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 428 expanded)
%              Number of leaves         :   43 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  242 (1986 expanded)
%              Number of equality atoms :   27 ( 176 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_152,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_116,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40,c_8])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k7_relat_1(B_21,A_20),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_119,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_tarski(A_93,C_94)
      | ~ r1_tarski(B_95,C_94)
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_119])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_238,plain,(
    ! [A_117,B_118,A_119] :
      ( v5_relat_1(A_117,B_118)
      | ~ r1_tarski(A_117,k2_zfmisc_1(A_119,B_118)) ) ),
    inference(resolution,[status(thm)],[c_6,c_169])).

tff(c_257,plain,(
    ! [A_93] :
      ( v5_relat_1(A_93,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_131,c_238])).

tff(c_203,plain,(
    ! [A_112] :
      ( r1_tarski(A_112,k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_112,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_119])).

tff(c_73,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_211,plain,(
    ! [A_112] :
      ( v1_relat_1(A_112)
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_112,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_203,c_80])).

tff(c_217,plain,(
    ! [A_113] :
      ( v1_relat_1(A_113)
      | ~ r1_tarski(A_113,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_211])).

tff(c_229,plain,(
    ! [A_20] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_20))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_234,plain,(
    ! [A_20] : v1_relat_1(k7_relat_1('#skF_4',A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_229])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_696,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( k2_partfun1(A_206,B_207,C_208,D_209) = k7_relat_1(C_208,D_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_700,plain,(
    ! [D_209] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_209) = k7_relat_1('#skF_4',D_209)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_696])).

tff(c_707,plain,(
    ! [D_209] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_209) = k7_relat_1('#skF_4',D_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_700])).

tff(c_900,plain,(
    ! [A_225,B_226,C_227,D_228] :
      ( k2_partfun1(u1_struct_0(A_225),u1_struct_0(B_226),C_227,u1_struct_0(D_228)) = k2_tmap_1(A_225,B_226,C_227,D_228)
      | ~ m1_pre_topc(D_228,A_225)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),u1_struct_0(B_226))))
      | ~ v1_funct_2(C_227,u1_struct_0(A_225),u1_struct_0(B_226))
      | ~ v1_funct_1(C_227)
      | ~ l1_pre_topc(B_226)
      | ~ v2_pre_topc(B_226)
      | v2_struct_0(B_226)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_905,plain,(
    ! [D_228] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_228)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_228)
      | ~ m1_pre_topc(D_228,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_900])).

tff(c_912,plain,(
    ! [D_228] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_228)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_228)
      | ~ m1_pre_topc(D_228,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58,c_56,c_44,c_42,c_707,c_905])).

tff(c_913,plain,(
    ! [D_228] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_228)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_228)
      | ~ m1_pre_topc(D_228,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_912])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_546,plain,(
    ! [C_175,A_176,B_177] :
      ( m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ r1_tarski(k2_relat_1(C_175),B_177)
      | ~ r1_tarski(k1_relat_1(C_175),A_176)
      | ~ v1_relat_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1037,plain,(
    ! [C_234,A_235,B_236] :
      ( r1_tarski(C_234,k2_zfmisc_1(A_235,B_236))
      | ~ r1_tarski(k2_relat_1(C_234),B_236)
      | ~ r1_tarski(k1_relat_1(C_234),A_235)
      | ~ v1_relat_1(C_234) ) ),
    inference(resolution,[status(thm)],[c_546,c_4])).

tff(c_1285,plain,(
    ! [B_259,A_260,A_261] :
      ( r1_tarski(B_259,k2_zfmisc_1(A_260,A_261))
      | ~ r1_tarski(k1_relat_1(B_259),A_260)
      | ~ v5_relat_1(B_259,A_261)
      | ~ v1_relat_1(B_259) ) ),
    inference(resolution,[status(thm)],[c_12,c_1037])).

tff(c_5425,plain,(
    ! [B_604,A_605,A_606] :
      ( r1_tarski(k7_relat_1(B_604,A_605),k2_zfmisc_1(A_605,A_606))
      | ~ v5_relat_1(k7_relat_1(B_604,A_605),A_606)
      | ~ v1_relat_1(k7_relat_1(B_604,A_605))
      | ~ v1_relat_1(B_604) ) ),
    inference(resolution,[status(thm)],[c_18,c_1285])).

tff(c_5452,plain,(
    ! [D_228,A_606] :
      ( r1_tarski(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_228),k2_zfmisc_1(u1_struct_0(D_228),A_606))
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_228)),A_606)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_228)))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_228,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_5425])).

tff(c_9271,plain,(
    ! [D_798,A_799] :
      ( r1_tarski(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_798),k2_zfmisc_1(u1_struct_0(D_798),A_799))
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_798)),A_799)
      | ~ m1_pre_topc(D_798,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_234,c_5452])).

tff(c_178,plain,(
    ! [A_4,B_104,A_105] :
      ( v5_relat_1(A_4,B_104)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_105,B_104)) ) ),
    inference(resolution,[status(thm)],[c_6,c_169])).

tff(c_9323,plain,(
    ! [D_800,A_801] :
      ( v5_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_800),A_801)
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_800)),A_801)
      | ~ m1_pre_topc(D_800,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_9271,c_178])).

tff(c_9373,plain,(
    ! [D_800] :
      ( v5_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_800),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_800,'#skF_2')
      | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0(D_800)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_257,c_9323])).

tff(c_917,plain,(
    ! [D_229] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_229)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229)
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_912])).

tff(c_93,plain,(
    ! [A_87,B_88] :
      ( v1_relat_1(A_87)
      | ~ v1_relat_1(B_88)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_109,plain,(
    ! [B_21,A_20] :
      ( v1_relat_1(k7_relat_1(B_21,A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_93])).

tff(c_968,plain,(
    ! [D_229] :
      ( v1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_109])).

tff(c_1006,plain,(
    ! [D_229] :
      ( v1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229))
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_968])).

tff(c_36,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_16,plain,(
    ! [A_13,C_17,B_16] :
      ( k9_relat_1(k7_relat_1(A_13,C_17),B_16) = k9_relat_1(A_13,B_16)
      | ~ r1_tarski(B_16,C_17)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_957,plain,(
    ! [D_229,B_16] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229),B_16) = k9_relat_1('#skF_4',B_16)
      | ~ r1_tarski(B_16,u1_struct_0(D_229))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_16])).

tff(c_2676,plain,(
    ! [D_376,B_377] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_376),B_377) = k9_relat_1('#skF_4',B_377)
      | ~ r1_tarski(B_377,u1_struct_0(D_376))
      | ~ m1_pre_topc(D_376,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_957])).

tff(c_2742,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_2676])).

tff(c_2769,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2742])).

tff(c_971,plain,(
    ! [D_229] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229)),u1_struct_0(D_229))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_18])).

tff(c_1008,plain,(
    ! [D_229] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229)),u1_struct_0(D_229))
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_971])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k7_relset_1(A_25,B_26,C_27,D_28) = k9_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1337,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k7_relset_1(A_265,B_266,C_267,D_268) = k9_relat_1(C_267,D_268)
      | ~ r1_tarski(k2_relat_1(C_267),B_266)
      | ~ r1_tarski(k1_relat_1(C_267),A_265)
      | ~ v1_relat_1(C_267) ) ),
    inference(resolution,[status(thm)],[c_546,c_26])).

tff(c_3257,plain,(
    ! [A_420,A_421,B_422,D_423] :
      ( k7_relset_1(A_420,A_421,B_422,D_423) = k9_relat_1(B_422,D_423)
      | ~ r1_tarski(k1_relat_1(B_422),A_420)
      | ~ v5_relat_1(B_422,A_421)
      | ~ v1_relat_1(B_422) ) ),
    inference(resolution,[status(thm)],[c_12,c_1337])).

tff(c_60551,plain,(
    ! [D_2708,A_2709,D_2710] :
      ( k7_relset_1(u1_struct_0(D_2708),A_2709,k2_tmap_1('#skF_2','#skF_1','#skF_4',D_2708),D_2710) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_2708),D_2710)
      | ~ v5_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_2708),A_2709)
      | ~ v1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_2708))
      | ~ m1_pre_topc(D_2708,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1008,c_3257])).

tff(c_426,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k7_relset_1(A_155,B_156,C_157,D_158) = k9_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_432,plain,(
    ! [D_158] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_158) = k9_relat_1('#skF_4',D_158) ),
    inference(resolution,[status(thm)],[c_40,c_426])).

tff(c_34,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_434,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_34])).

tff(c_60589,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60551,c_434])).

tff(c_60634,plain,
    ( ~ v5_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2769,c_60589])).

tff(c_60643,plain,(
    ~ v1_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60634])).

tff(c_60646,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1006,c_60643])).

tff(c_60650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60646])).

tff(c_60651,plain,(
    ~ v5_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_60634])).

tff(c_61013,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9373,c_60651])).

tff(c_61025,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_61013])).

tff(c_61035,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_61025])).

tff(c_61041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_61035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:28:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.46/20.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.46/20.68  
% 30.46/20.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.46/20.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 30.46/20.68  
% 30.46/20.68  %Foreground sorts:
% 30.46/20.68  
% 30.46/20.68  
% 30.46/20.68  %Background operators:
% 30.46/20.68  
% 30.46/20.68  
% 30.46/20.68  %Foreground operators:
% 30.46/20.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 30.46/20.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.46/20.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.46/20.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 30.46/20.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 30.46/20.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.46/20.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.46/20.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 30.46/20.68  tff('#skF_5', type, '#skF_5': $i).
% 30.46/20.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 30.46/20.68  tff('#skF_2', type, '#skF_2': $i).
% 30.46/20.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 30.46/20.68  tff('#skF_3', type, '#skF_3': $i).
% 30.46/20.68  tff('#skF_1', type, '#skF_1': $i).
% 30.46/20.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 30.46/20.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.46/20.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.46/20.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.46/20.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.46/20.68  tff('#skF_4', type, '#skF_4': $i).
% 30.46/20.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.46/20.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 30.46/20.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 30.46/20.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 30.46/20.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 30.46/20.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 30.46/20.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 30.46/20.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.46/20.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.46/20.68  
% 30.69/20.70  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 30.69/20.70  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 30.69/20.70  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 30.69/20.70  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 30.69/20.70  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 30.69/20.70  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 30.69/20.70  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 30.69/20.70  tff(f_89, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 30.69/20.70  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 30.69/20.70  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 30.69/20.70  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 30.69/20.70  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 30.69/20.70  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 30.75/20.70  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 30.75/20.70  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 30.75/20.70  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_8, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 30.75/20.70  tff(c_85, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_8])).
% 30.75/20.70  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_85])).
% 30.75/20.70  tff(c_20, plain, (![B_21, A_20]: (r1_tarski(k7_relat_1(B_21, A_20), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.75/20.70  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.75/20.70  tff(c_92, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_4])).
% 30.75/20.70  tff(c_119, plain, (![A_93, C_94, B_95]: (r1_tarski(A_93, C_94) | ~r1_tarski(B_95, C_94) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.75/20.70  tff(c_131, plain, (![A_93]: (r1_tarski(A_93, k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))) | ~r1_tarski(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_119])).
% 30.75/20.70  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.75/20.70  tff(c_169, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.75/20.70  tff(c_238, plain, (![A_117, B_118, A_119]: (v5_relat_1(A_117, B_118) | ~r1_tarski(A_117, k2_zfmisc_1(A_119, B_118)))), inference(resolution, [status(thm)], [c_6, c_169])).
% 30.75/20.70  tff(c_257, plain, (![A_93]: (v5_relat_1(A_93, u1_struct_0('#skF_1')) | ~r1_tarski(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_131, c_238])).
% 30.75/20.70  tff(c_203, plain, (![A_112]: (r1_tarski(A_112, k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))) | ~r1_tarski(A_112, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_119])).
% 30.75/20.70  tff(c_73, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_42])).
% 30.75/20.70  tff(c_80, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_73])).
% 30.75/20.70  tff(c_211, plain, (![A_112]: (v1_relat_1(A_112) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))) | ~r1_tarski(A_112, '#skF_4'))), inference(resolution, [status(thm)], [c_203, c_80])).
% 30.75/20.70  tff(c_217, plain, (![A_113]: (v1_relat_1(A_113) | ~r1_tarski(A_113, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_211])).
% 30.75/20.70  tff(c_229, plain, (![A_20]: (v1_relat_1(k7_relat_1('#skF_4', A_20)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_217])).
% 30.75/20.70  tff(c_234, plain, (![A_20]: (v1_relat_1(k7_relat_1('#skF_4', A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_229])).
% 30.75/20.70  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_696, plain, (![A_206, B_207, C_208, D_209]: (k2_partfun1(A_206, B_207, C_208, D_209)=k7_relat_1(C_208, D_209) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_1(C_208))), inference(cnfTransformation, [status(thm)], [f_89])).
% 30.75/20.70  tff(c_700, plain, (![D_209]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_209)=k7_relat_1('#skF_4', D_209) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_696])).
% 30.75/20.70  tff(c_707, plain, (![D_209]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_209)=k7_relat_1('#skF_4', D_209))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_700])).
% 30.75/20.70  tff(c_900, plain, (![A_225, B_226, C_227, D_228]: (k2_partfun1(u1_struct_0(A_225), u1_struct_0(B_226), C_227, u1_struct_0(D_228))=k2_tmap_1(A_225, B_226, C_227, D_228) | ~m1_pre_topc(D_228, A_225) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), u1_struct_0(B_226)))) | ~v1_funct_2(C_227, u1_struct_0(A_225), u1_struct_0(B_226)) | ~v1_funct_1(C_227) | ~l1_pre_topc(B_226) | ~v2_pre_topc(B_226) | v2_struct_0(B_226) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_116])).
% 30.75/20.70  tff(c_905, plain, (![D_228]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_228))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_228) | ~m1_pre_topc(D_228, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_900])).
% 30.75/20.70  tff(c_912, plain, (![D_228]: (k7_relat_1('#skF_4', u1_struct_0(D_228))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_228) | ~m1_pre_topc(D_228, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58, c_56, c_44, c_42, c_707, c_905])).
% 30.75/20.70  tff(c_913, plain, (![D_228]: (k7_relat_1('#skF_4', u1_struct_0(D_228))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_228) | ~m1_pre_topc(D_228, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_60, c_912])).
% 30.75/20.70  tff(c_18, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 30.75/20.70  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 30.75/20.70  tff(c_546, plain, (![C_175, A_176, B_177]: (m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~r1_tarski(k2_relat_1(C_175), B_177) | ~r1_tarski(k1_relat_1(C_175), A_176) | ~v1_relat_1(C_175))), inference(cnfTransformation, [status(thm)], [f_83])).
% 30.75/20.70  tff(c_1037, plain, (![C_234, A_235, B_236]: (r1_tarski(C_234, k2_zfmisc_1(A_235, B_236)) | ~r1_tarski(k2_relat_1(C_234), B_236) | ~r1_tarski(k1_relat_1(C_234), A_235) | ~v1_relat_1(C_234))), inference(resolution, [status(thm)], [c_546, c_4])).
% 30.75/20.70  tff(c_1285, plain, (![B_259, A_260, A_261]: (r1_tarski(B_259, k2_zfmisc_1(A_260, A_261)) | ~r1_tarski(k1_relat_1(B_259), A_260) | ~v5_relat_1(B_259, A_261) | ~v1_relat_1(B_259))), inference(resolution, [status(thm)], [c_12, c_1037])).
% 30.75/20.70  tff(c_5425, plain, (![B_604, A_605, A_606]: (r1_tarski(k7_relat_1(B_604, A_605), k2_zfmisc_1(A_605, A_606)) | ~v5_relat_1(k7_relat_1(B_604, A_605), A_606) | ~v1_relat_1(k7_relat_1(B_604, A_605)) | ~v1_relat_1(B_604))), inference(resolution, [status(thm)], [c_18, c_1285])).
% 30.75/20.70  tff(c_5452, plain, (![D_228, A_606]: (r1_tarski(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_228), k2_zfmisc_1(u1_struct_0(D_228), A_606)) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_228)), A_606) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_228))) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_228, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_913, c_5425])).
% 30.75/20.70  tff(c_9271, plain, (![D_798, A_799]: (r1_tarski(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_798), k2_zfmisc_1(u1_struct_0(D_798), A_799)) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_798)), A_799) | ~m1_pre_topc(D_798, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_234, c_5452])).
% 30.75/20.70  tff(c_178, plain, (![A_4, B_104, A_105]: (v5_relat_1(A_4, B_104) | ~r1_tarski(A_4, k2_zfmisc_1(A_105, B_104)))), inference(resolution, [status(thm)], [c_6, c_169])).
% 30.75/20.70  tff(c_9323, plain, (![D_800, A_801]: (v5_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_800), A_801) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_800)), A_801) | ~m1_pre_topc(D_800, '#skF_2'))), inference(resolution, [status(thm)], [c_9271, c_178])).
% 30.75/20.70  tff(c_9373, plain, (![D_800]: (v5_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_800), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_800, '#skF_2') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0(D_800)), '#skF_4'))), inference(resolution, [status(thm)], [c_257, c_9323])).
% 30.75/20.70  tff(c_917, plain, (![D_229]: (k7_relat_1('#skF_4', u1_struct_0(D_229))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229) | ~m1_pre_topc(D_229, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_60, c_912])).
% 30.75/20.70  tff(c_93, plain, (![A_87, B_88]: (v1_relat_1(A_87) | ~v1_relat_1(B_88) | ~r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_6, c_73])).
% 30.75/20.70  tff(c_109, plain, (![B_21, A_20]: (v1_relat_1(k7_relat_1(B_21, A_20)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_20, c_93])).
% 30.75/20.70  tff(c_968, plain, (![D_229]: (v1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_229, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_917, c_109])).
% 30.75/20.70  tff(c_1006, plain, (![D_229]: (v1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229)) | ~m1_pre_topc(D_229, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_968])).
% 30.75/20.70  tff(c_36, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_16, plain, (![A_13, C_17, B_16]: (k9_relat_1(k7_relat_1(A_13, C_17), B_16)=k9_relat_1(A_13, B_16) | ~r1_tarski(B_16, C_17) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.75/20.70  tff(c_957, plain, (![D_229, B_16]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229), B_16)=k9_relat_1('#skF_4', B_16) | ~r1_tarski(B_16, u1_struct_0(D_229)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_229, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_917, c_16])).
% 30.75/20.70  tff(c_2676, plain, (![D_376, B_377]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_376), B_377)=k9_relat_1('#skF_4', B_377) | ~r1_tarski(B_377, u1_struct_0(D_376)) | ~m1_pre_topc(D_376, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_957])).
% 30.75/20.70  tff(c_2742, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_2676])).
% 30.75/20.70  tff(c_2769, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2742])).
% 30.75/20.70  tff(c_971, plain, (![D_229]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229)), u1_struct_0(D_229)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_229, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_917, c_18])).
% 30.75/20.70  tff(c_1008, plain, (![D_229]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229)), u1_struct_0(D_229)) | ~m1_pre_topc(D_229, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_971])).
% 30.75/20.70  tff(c_26, plain, (![A_25, B_26, C_27, D_28]: (k7_relset_1(A_25, B_26, C_27, D_28)=k9_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 30.75/20.70  tff(c_1337, plain, (![A_265, B_266, C_267, D_268]: (k7_relset_1(A_265, B_266, C_267, D_268)=k9_relat_1(C_267, D_268) | ~r1_tarski(k2_relat_1(C_267), B_266) | ~r1_tarski(k1_relat_1(C_267), A_265) | ~v1_relat_1(C_267))), inference(resolution, [status(thm)], [c_546, c_26])).
% 30.75/20.70  tff(c_3257, plain, (![A_420, A_421, B_422, D_423]: (k7_relset_1(A_420, A_421, B_422, D_423)=k9_relat_1(B_422, D_423) | ~r1_tarski(k1_relat_1(B_422), A_420) | ~v5_relat_1(B_422, A_421) | ~v1_relat_1(B_422))), inference(resolution, [status(thm)], [c_12, c_1337])).
% 30.75/20.70  tff(c_60551, plain, (![D_2708, A_2709, D_2710]: (k7_relset_1(u1_struct_0(D_2708), A_2709, k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_2708), D_2710)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_2708), D_2710) | ~v5_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_2708), A_2709) | ~v1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_2708)) | ~m1_pre_topc(D_2708, '#skF_2'))), inference(resolution, [status(thm)], [c_1008, c_3257])).
% 30.75/20.70  tff(c_426, plain, (![A_155, B_156, C_157, D_158]: (k7_relset_1(A_155, B_156, C_157, D_158)=k9_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 30.75/20.70  tff(c_432, plain, (![D_158]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_158)=k9_relat_1('#skF_4', D_158))), inference(resolution, [status(thm)], [c_40, c_426])).
% 30.75/20.70  tff(c_34, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 30.75/20.70  tff(c_434, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_34])).
% 30.75/20.70  tff(c_60589, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v5_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_1')) | ~v1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60551, c_434])).
% 30.75/20.70  tff(c_60634, plain, (~v5_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_1')) | ~v1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2769, c_60589])).
% 30.75/20.70  tff(c_60643, plain, (~v1_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_60634])).
% 30.75/20.70  tff(c_60646, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1006, c_60643])).
% 30.75/20.70  tff(c_60650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_60646])).
% 30.75/20.70  tff(c_60651, plain, (~v5_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_60634])).
% 30.75/20.70  tff(c_61013, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(resolution, [status(thm)], [c_9373, c_60651])).
% 30.75/20.70  tff(c_61025, plain, (~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_61013])).
% 30.75/20.70  tff(c_61035, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_61025])).
% 30.75/20.70  tff(c_61041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_61035])).
% 30.75/20.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.75/20.70  
% 30.75/20.70  Inference rules
% 30.75/20.70  ----------------------
% 30.75/20.70  #Ref     : 0
% 30.75/20.70  #Sup     : 15330
% 30.75/20.70  #Fact    : 0
% 30.75/20.70  #Define  : 0
% 30.75/20.70  #Split   : 27
% 30.75/20.70  #Chain   : 0
% 30.75/20.70  #Close   : 0
% 30.75/20.70  
% 30.75/20.70  Ordering : KBO
% 30.75/20.70  
% 30.75/20.70  Simplification rules
% 30.75/20.70  ----------------------
% 30.75/20.70  #Subsume      : 2718
% 30.75/20.70  #Demod        : 2697
% 30.75/20.70  #Tautology    : 950
% 30.75/20.70  #SimpNegUnit  : 441
% 30.75/20.70  #BackRed      : 1
% 30.75/20.70  
% 30.75/20.70  #Partial instantiations: 0
% 30.75/20.70  #Strategies tried      : 1
% 30.75/20.70  
% 30.75/20.70  Timing (in seconds)
% 30.75/20.70  ----------------------
% 30.75/20.70  Preprocessing        : 0.35
% 30.75/20.70  Parsing              : 0.19
% 30.75/20.70  CNF conversion       : 0.03
% 30.75/20.70  Main loop            : 19.59
% 30.75/20.70  Inferencing          : 3.39
% 30.75/20.70  Reduction            : 4.43
% 30.75/20.70  Demodulation         : 3.06
% 30.75/20.70  BG Simplification    : 0.32
% 30.75/20.70  Subsumption          : 10.30
% 30.75/20.70  Abstraction          : 0.56
% 30.75/20.70  MUC search           : 0.00
% 30.75/20.70  Cooper               : 0.00
% 30.75/20.70  Total                : 19.98
% 30.75/20.70  Index Insertion      : 0.00
% 30.75/20.70  Index Deletion       : 0.00
% 30.75/20.70  Index Matching       : 0.00
% 30.75/20.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
