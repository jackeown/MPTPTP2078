%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:25 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 288 expanded)
%              Number of leaves         :   42 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 799 expanded)
%              Number of equality atoms :   29 ( 108 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_84,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v2_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_tops_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_22,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_1'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_57,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_1'(A_19),A_19)
      | A_19 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_28,plain,(
    ! [A_43] :
      ( v4_pre_topc(k2_struct_0(A_43),A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_26,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_101,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_107,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_111,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_112,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_42])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_141,plain,(
    ! [C_74,B_75,A_76] :
      ( ~ v1_xboole_0(C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    ! [A_5,A_76] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_141])).

tff(c_154,plain,(
    ! [A_76] : ~ r2_hidden(A_76,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_64,plain,(
    ! [A_1] : k1_subset_1(A_1) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_4] : k3_subset_1(A_4,k1_subset_1(A_4)) = k2_subset_1(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_4] : k3_subset_1(A_4,k1_subset_1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_65,plain,(
    ! [A_4] : k3_subset_1(A_4,'#skF_5') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63])).

tff(c_14,plain,(
    ! [C_12,A_6,B_10] :
      ( r2_hidden(C_12,k3_subset_1(A_6,B_10))
      | r2_hidden(C_12,B_10)
      | ~ m1_subset_1(C_12,A_6)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_6))
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_329,plain,(
    ! [C_101,A_102,B_103] :
      ( r2_hidden(C_101,k3_subset_1(A_102,B_103))
      | r2_hidden(C_101,B_103)
      | ~ m1_subset_1(C_101,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102))
      | A_102 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_338,plain,(
    ! [C_101,A_4] :
      ( r2_hidden(C_101,A_4)
      | r2_hidden(C_101,'#skF_5')
      | ~ m1_subset_1(C_101,A_4)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4))
      | A_4 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_329])).

tff(c_342,plain,(
    ! [C_101,A_4] :
      ( r2_hidden(C_101,A_4)
      | r2_hidden(C_101,'#skF_5')
      | ~ m1_subset_1(C_101,A_4)
      | A_4 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_338])).

tff(c_343,plain,(
    ! [C_101,A_4] :
      ( r2_hidden(C_101,A_4)
      | ~ m1_subset_1(C_101,A_4)
      | A_4 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_342])).

tff(c_30,plain,(
    ! [A_44] :
      ( v3_pre_topc(k2_struct_0(A_44),A_44)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_50,plain,(
    ! [D_59] :
      ( r2_hidden(D_59,'#skF_5')
      | ~ r2_hidden('#skF_4',D_59)
      | ~ v4_pre_topc(D_59,'#skF_3')
      | ~ v3_pre_topc(D_59,'#skF_3')
      | ~ m1_subset_1(D_59,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_281,plain,(
    ! [D_59] :
      ( r2_hidden(D_59,'#skF_5')
      | ~ r2_hidden('#skF_4',D_59)
      | ~ v4_pre_topc(D_59,'#skF_3')
      | ~ v3_pre_topc(D_59,'#skF_3')
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50])).

tff(c_283,plain,(
    ! [D_97] :
      ( ~ r2_hidden('#skF_4',D_97)
      | ~ v4_pre_topc(D_97,'#skF_3')
      | ~ v3_pre_topc(D_97,'#skF_3')
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_281])).

tff(c_298,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_283])).

tff(c_319,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_322,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_319])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_322])).

tff(c_327,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_379,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_382,plain,
    ( ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_343,c_379])).

tff(c_385,plain,(
    k2_struct_0('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_382])).

tff(c_131,plain,(
    ! [A_73] :
      ( m1_subset_1('#skF_2'(A_73),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_134,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_131])).

tff(c_136,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_134])).

tff(c_150,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_76,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_136,c_141])).

tff(c_174,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_390,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_174])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_390])).

tff(c_396,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_400,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_396])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_400])).

tff(c_450,plain,(
    ! [A_109] : ~ r2_hidden(A_109,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_455,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_57,c_450])).

tff(c_32,plain,(
    ! [A_45] :
      ( v2_tops_1('#skF_2'(A_45),A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_463,plain,
    ( v2_tops_1('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_32])).

tff(c_469,plain,(
    v2_tops_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_463])).

tff(c_406,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_162,plain,(
    ! [A_78,A_79] :
      ( ~ v1_xboole_0(A_78)
      | ~ r2_hidden(A_79,A_78) ) ),
    inference(resolution,[status(thm)],[c_62,c_141])).

tff(c_166,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(A_19)
      | A_19 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_57,c_162])).

tff(c_410,plain,(
    k2_struct_0('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_406,c_166])).

tff(c_473,plain,(
    ! [A_110] :
      ( ~ v2_tops_1(k2_struct_0(A_110),A_110)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_476,plain,
    ( ~ v2_tops_1('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_473])).

tff(c_478,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_469,c_476])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_478])).

tff(c_481,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.41  
% 2.68/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.41  %$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.68/1.41  
% 2.68/1.41  %Foreground sorts:
% 2.68/1.41  
% 2.68/1.41  
% 2.68/1.41  %Background operators:
% 2.68/1.41  
% 2.68/1.41  
% 2.68/1.41  %Foreground operators:
% 2.68/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.68/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.41  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.68/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.68/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.68/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.68/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.68/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.68/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.41  
% 2.68/1.43  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.68/1.43  tff(f_84, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.68/1.43  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.68/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.43  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.68/1.43  tff(f_88, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.68/1.43  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.43  tff(f_63, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.68/1.43  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.68/1.43  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.68/1.43  tff(f_34, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.68/1.43  tff(f_50, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.68/1.43  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.68/1.43  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.68/1.43  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v2_tops_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_tops_1)).
% 2.68/1.43  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ~v2_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_tops_1)).
% 2.68/1.43  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.68/1.43  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.68/1.43  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.68/1.43  tff(c_38, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.68/1.43  tff(c_22, plain, (![A_19]: (r2_hidden('#skF_1'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.68/1.43  tff(c_57, plain, (![A_19]: (r2_hidden('#skF_1'(A_19), A_19) | A_19='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22])).
% 2.68/1.43  tff(c_28, plain, (![A_43]: (v4_pre_topc(k2_struct_0(A_43), A_43) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.43  tff(c_66, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 2.68/1.43  tff(c_26, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.68/1.43  tff(c_101, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.68/1.43  tff(c_107, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_26, c_101])).
% 2.68/1.43  tff(c_111, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_107])).
% 2.68/1.43  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.68/1.43  tff(c_112, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_42])).
% 2.68/1.43  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.43  tff(c_60, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 2.68/1.43  tff(c_141, plain, (![C_74, B_75, A_76]: (~v1_xboole_0(C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.68/1.43  tff(c_152, plain, (![A_5, A_76]: (~v1_xboole_0(A_5) | ~r2_hidden(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_141])).
% 2.68/1.43  tff(c_154, plain, (![A_76]: (~r2_hidden(A_76, '#skF_5'))), inference(splitLeft, [status(thm)], [c_152])).
% 2.68/1.43  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.68/1.43  tff(c_64, plain, (![A_1]: (k1_subset_1(A_1)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4])).
% 2.68/1.43  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.43  tff(c_10, plain, (![A_4]: (k3_subset_1(A_4, k1_subset_1(A_4))=k2_subset_1(A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.43  tff(c_63, plain, (![A_4]: (k3_subset_1(A_4, k1_subset_1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.68/1.43  tff(c_65, plain, (![A_4]: (k3_subset_1(A_4, '#skF_5')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63])).
% 2.68/1.43  tff(c_14, plain, (![C_12, A_6, B_10]: (r2_hidden(C_12, k3_subset_1(A_6, B_10)) | r2_hidden(C_12, B_10) | ~m1_subset_1(C_12, A_6) | ~m1_subset_1(B_10, k1_zfmisc_1(A_6)) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.43  tff(c_329, plain, (![C_101, A_102, B_103]: (r2_hidden(C_101, k3_subset_1(A_102, B_103)) | r2_hidden(C_101, B_103) | ~m1_subset_1(C_101, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)) | A_102='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 2.68/1.43  tff(c_338, plain, (![C_101, A_4]: (r2_hidden(C_101, A_4) | r2_hidden(C_101, '#skF_5') | ~m1_subset_1(C_101, A_4) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4)) | A_4='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_65, c_329])).
% 2.68/1.43  tff(c_342, plain, (![C_101, A_4]: (r2_hidden(C_101, A_4) | r2_hidden(C_101, '#skF_5') | ~m1_subset_1(C_101, A_4) | A_4='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_338])).
% 2.68/1.43  tff(c_343, plain, (![C_101, A_4]: (r2_hidden(C_101, A_4) | ~m1_subset_1(C_101, A_4) | A_4='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_154, c_342])).
% 2.68/1.43  tff(c_30, plain, (![A_44]: (v3_pre_topc(k2_struct_0(A_44), A_44) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.43  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.43  tff(c_62, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.68/1.43  tff(c_50, plain, (![D_59]: (r2_hidden(D_59, '#skF_5') | ~r2_hidden('#skF_4', D_59) | ~v4_pre_topc(D_59, '#skF_3') | ~v3_pre_topc(D_59, '#skF_3') | ~m1_subset_1(D_59, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.68/1.43  tff(c_281, plain, (![D_59]: (r2_hidden(D_59, '#skF_5') | ~r2_hidden('#skF_4', D_59) | ~v4_pre_topc(D_59, '#skF_3') | ~v3_pre_topc(D_59, '#skF_3') | ~m1_subset_1(D_59, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_50])).
% 2.68/1.43  tff(c_283, plain, (![D_97]: (~r2_hidden('#skF_4', D_97) | ~v4_pre_topc(D_97, '#skF_3') | ~v3_pre_topc(D_97, '#skF_3') | ~m1_subset_1(D_97, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_154, c_281])).
% 2.68/1.43  tff(c_298, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_62, c_283])).
% 2.68/1.43  tff(c_319, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_298])).
% 2.68/1.43  tff(c_322, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_319])).
% 2.68/1.43  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_322])).
% 2.68/1.43  tff(c_327, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_298])).
% 2.68/1.43  tff(c_379, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_327])).
% 2.68/1.43  tff(c_382, plain, (~m1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_343, c_379])).
% 2.68/1.43  tff(c_385, plain, (k2_struct_0('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_382])).
% 2.68/1.43  tff(c_131, plain, (![A_73]: (m1_subset_1('#skF_2'(A_73), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.43  tff(c_134, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_131])).
% 2.68/1.43  tff(c_136, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_134])).
% 2.68/1.43  tff(c_150, plain, (![A_76]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_76, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_136, c_141])).
% 2.68/1.43  tff(c_174, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_150])).
% 2.68/1.43  tff(c_390, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_174])).
% 2.68/1.43  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_390])).
% 2.68/1.43  tff(c_396, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_327])).
% 2.68/1.43  tff(c_400, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_396])).
% 2.68/1.43  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_400])).
% 2.68/1.43  tff(c_450, plain, (![A_109]: (~r2_hidden(A_109, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_150])).
% 2.68/1.43  tff(c_455, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_57, c_450])).
% 2.68/1.43  tff(c_32, plain, (![A_45]: (v2_tops_1('#skF_2'(A_45), A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.43  tff(c_463, plain, (v2_tops_1('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_455, c_32])).
% 2.68/1.43  tff(c_469, plain, (v2_tops_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_463])).
% 2.68/1.43  tff(c_406, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_150])).
% 2.68/1.43  tff(c_162, plain, (![A_78, A_79]: (~v1_xboole_0(A_78) | ~r2_hidden(A_79, A_78))), inference(resolution, [status(thm)], [c_62, c_141])).
% 2.68/1.43  tff(c_166, plain, (![A_19]: (~v1_xboole_0(A_19) | A_19='#skF_5')), inference(resolution, [status(thm)], [c_57, c_162])).
% 2.68/1.43  tff(c_410, plain, (k2_struct_0('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_406, c_166])).
% 2.68/1.43  tff(c_473, plain, (![A_110]: (~v2_tops_1(k2_struct_0(A_110), A_110) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.43  tff(c_476, plain, (~v2_tops_1('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_410, c_473])).
% 2.68/1.43  tff(c_478, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_469, c_476])).
% 2.68/1.43  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_478])).
% 2.68/1.43  tff(c_481, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitRight, [status(thm)], [c_152])).
% 2.68/1.43  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_66])).
% 2.68/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  Inference rules
% 2.68/1.43  ----------------------
% 2.68/1.43  #Ref     : 0
% 2.68/1.43  #Sup     : 83
% 2.68/1.43  #Fact    : 0
% 2.68/1.43  #Define  : 0
% 2.68/1.43  #Split   : 7
% 2.68/1.43  #Chain   : 0
% 2.68/1.43  #Close   : 0
% 2.68/1.43  
% 2.68/1.43  Ordering : KBO
% 2.68/1.43  
% 2.68/1.43  Simplification rules
% 2.68/1.43  ----------------------
% 2.68/1.43  #Subsume      : 22
% 2.68/1.43  #Demod        : 69
% 2.68/1.43  #Tautology    : 34
% 2.68/1.43  #SimpNegUnit  : 4
% 2.68/1.43  #BackRed      : 15
% 2.68/1.43  
% 2.68/1.43  #Partial instantiations: 0
% 2.68/1.43  #Strategies tried      : 1
% 2.68/1.43  
% 2.68/1.43  Timing (in seconds)
% 2.68/1.43  ----------------------
% 2.68/1.43  Preprocessing        : 0.35
% 2.68/1.43  Parsing              : 0.18
% 2.68/1.43  CNF conversion       : 0.03
% 2.68/1.43  Main loop            : 0.30
% 2.68/1.43  Inferencing          : 0.10
% 2.68/1.43  Reduction            : 0.10
% 2.68/1.43  Demodulation         : 0.07
% 2.68/1.44  BG Simplification    : 0.02
% 2.68/1.44  Subsumption          : 0.05
% 2.68/1.44  Abstraction          : 0.01
% 2.68/1.44  MUC search           : 0.00
% 2.68/1.44  Cooper               : 0.00
% 2.68/1.44  Total                : 0.69
% 2.68/1.44  Index Insertion      : 0.00
% 2.68/1.44  Index Deletion       : 0.00
% 2.68/1.44  Index Matching       : 0.00
% 2.68/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
