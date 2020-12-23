%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 795 expanded)
%              Number of leaves         :   39 ( 290 expanded)
%              Depth                    :   14
%              Number of atoms          :  409 (1967 expanded)
%              Number of equality atoms :   73 ( 431 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_20,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_87,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_83])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_82,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_100,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_82])).

tff(c_56,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_121,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_87,c_56])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_88,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_48])).

tff(c_1827,plain,(
    ! [B_134,A_135] :
      ( v3_pre_topc(B_134,A_135)
      | ~ r2_hidden(B_134,u1_pre_topc(A_135))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1830,plain,(
    ! [B_134] :
      ( v3_pre_topc(B_134,'#skF_1')
      | ~ r2_hidden(B_134,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1827])).

tff(c_1859,plain,(
    ! [B_138] :
      ( v3_pre_topc(B_138,'#skF_1')
      | ~ r2_hidden(B_138,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1830])).

tff(c_1862,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_88,c_1859])).

tff(c_1869,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_1862])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2866,plain,(
    ! [B_174,A_175] :
      ( r2_hidden(B_174,u1_pre_topc(A_175))
      | k5_tmap_1(A_175,B_174) != u1_pre_topc(A_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2881,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_174) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2866])).

tff(c_2892,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_174) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2881])).

tff(c_3172,plain,(
    ! [B_186] :
      ( r2_hidden(B_186,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_186) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2892])).

tff(c_3175,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_3172])).

tff(c_3182,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1869,c_3175])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_161,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,u1_pre_topc(A_53))
      | ~ v3_pre_topc(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_173,plain,(
    ! [A_54] :
      ( r2_hidden(u1_struct_0(A_54),u1_pre_topc(A_54))
      | ~ v3_pre_topc(u1_struct_0(A_54),A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_63,c_161])).

tff(c_176,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_173])).

tff(c_178,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_87,c_176])).

tff(c_179,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_322,plain,(
    ! [A_74,B_75] :
      ( m2_connsp_2(k2_struct_0(A_74),A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_324,plain,(
    ! [B_75] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_322])).

tff(c_329,plain,(
    ! [B_75] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_324])).

tff(c_350,plain,(
    ! [B_77] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_329])).

tff(c_359,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_63,c_350])).

tff(c_1375,plain,(
    ! [B_109,A_110,C_111] :
      ( r1_tarski(B_109,k1_tops_1(A_110,C_111))
      | ~ m2_connsp_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1387,plain,(
    ! [B_109,C_111] :
      ( r1_tarski(B_109,k1_tops_1('#skF_1',C_111))
      | ~ m2_connsp_2(C_111,'#skF_1',B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1375])).

tff(c_1402,plain,(
    ! [B_112,C_113] :
      ( r1_tarski(B_112,k1_tops_1('#skF_1',C_113))
      | ~ m2_connsp_2(C_113,'#skF_1',B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_87,c_1387])).

tff(c_1734,plain,(
    ! [B_123] :
      ( r1_tarski(B_123,k1_tops_1('#skF_1',k2_struct_0('#skF_1')))
      | ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_63,c_1402])).

tff(c_122,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tops_1(A_48,B_49),B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    ! [A_50] :
      ( r1_tarski(k1_tops_1(A_50,u1_struct_0(A_50)),u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_63,c_122])).

tff(c_136,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_struct_0('#skF_1')),u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_131])).

tff(c_142,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_87,c_136])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,
    ( k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_190,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_1739,plain,
    ( ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1734,c_190])).

tff(c_1748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_359,c_1739])).

tff(c_1749,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_1780,plain,(
    ! [A_127,B_128] :
      ( v3_pre_topc(k1_tops_1(A_127,B_128),A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1789,plain,(
    ! [A_129] :
      ( v3_pre_topc(k1_tops_1(A_129,u1_struct_0(A_129)),A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_63,c_1780])).

tff(c_1792,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_struct_0('#skF_1')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1789])).

tff(c_1794,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1749,c_1792])).

tff(c_1796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_1794])).

tff(c_1797,plain,(
    r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_3137,plain,(
    ! [A_183,B_184] :
      ( k5_tmap_1(A_183,B_184) = u1_pre_topc(A_183)
      | ~ r2_hidden(B_184,u1_pre_topc(A_183))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3152,plain,(
    ! [B_184] :
      ( k5_tmap_1('#skF_1',B_184) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_184,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_3137])).

tff(c_3163,plain,(
    ! [B_184] :
      ( k5_tmap_1('#skF_1',B_184) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_184,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3152])).

tff(c_3445,plain,(
    ! [B_193] :
      ( k5_tmap_1('#skF_1',B_193) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_193,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3163])).

tff(c_3452,plain,
    ( k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_63,c_3445])).

tff(c_3457,plain,(
    k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_3452])).

tff(c_1873,plain,(
    ! [A_139,B_140] :
      ( l1_pre_topc(k6_tmap_1(A_139,B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1876,plain,(
    ! [B_140] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1873])).

tff(c_1882,plain,(
    ! [B_140] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1876])).

tff(c_1885,plain,(
    ! [B_141] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1882])).

tff(c_1894,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_63,c_1885])).

tff(c_1903,plain,(
    ! [A_142,B_143] :
      ( v1_pre_topc(k6_tmap_1(A_142,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1906,plain,(
    ! [B_143] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1903])).

tff(c_1912,plain,(
    ! [B_143] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1906])).

tff(c_1977,plain,(
    ! [B_144] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1912])).

tff(c_1986,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_63,c_1977])).

tff(c_2329,plain,(
    ! [A_159,B_160] :
      ( u1_struct_0(k6_tmap_1(A_159,B_160)) = u1_struct_0(A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2341,plain,(
    ! [B_160] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_160)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2329])).

tff(c_2351,plain,(
    ! [B_160] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_160)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_87,c_2341])).

tff(c_2354,plain,(
    ! [B_161] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_161)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2351])).

tff(c_2363,plain,(
    u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_2354])).

tff(c_2729,plain,(
    ! [A_168,B_169] :
      ( u1_pre_topc(k6_tmap_1(A_168,B_169)) = k5_tmap_1(A_168,B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2744,plain,(
    ! [B_169] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_169)) = k5_tmap_1('#skF_1',B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2729])).

tff(c_2755,plain,(
    ! [B_169] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_169)) = k5_tmap_1('#skF_1',B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2744])).

tff(c_2808,plain,(
    ! [B_173] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_173)) = k5_tmap_1('#skF_1',B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2755])).

tff(c_2817,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_63,c_2808])).

tff(c_12,plain,(
    ! [A_5] :
      ( g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) = A_5
      | ~ v1_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2847,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))),k5_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2817,c_12])).

tff(c_2855,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_1986,c_2363,c_2847])).

tff(c_3458,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3457,c_2855])).

tff(c_3460,plain,(
    k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3458])).

tff(c_3459,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3457,c_2817])).

tff(c_3485,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3460,c_3459])).

tff(c_2816,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_2808])).

tff(c_3531,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3485,c_2816])).

tff(c_3533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3182,c_3531])).

tff(c_3534,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3536,plain,(
    ! [A_194] :
      ( u1_struct_0(A_194) = k2_struct_0(A_194)
      | ~ l1_pre_topc(A_194) ) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_3540,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3536])).

tff(c_3547,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_3540,c_56])).

tff(c_3541,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3540,c_48])).

tff(c_3638,plain,(
    ! [B_206,A_207] :
      ( r2_hidden(B_206,u1_pre_topc(A_207))
      | ~ v3_pre_topc(B_206,A_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3641,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_206,'#skF_1')
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_3638])).

tff(c_3656,plain,(
    ! [B_209] :
      ( r2_hidden(B_209,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_209,'#skF_1')
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3641])).

tff(c_3659,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3541,c_3656])).

tff(c_3666,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_3659])).

tff(c_4672,plain,(
    ! [A_251,B_252] :
      ( k5_tmap_1(A_251,B_252) = u1_pre_topc(A_251)
      | ~ r2_hidden(B_252,u1_pre_topc(A_251))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4687,plain,(
    ! [B_252] :
      ( k5_tmap_1('#skF_1',B_252) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_252,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_4672])).

tff(c_4698,plain,(
    ! [B_252] :
      ( k5_tmap_1('#skF_1',B_252) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_252,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4687])).

tff(c_4807,plain,(
    ! [B_255] :
      ( k5_tmap_1('#skF_1',B_255) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_255,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4698])).

tff(c_4810,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3541,c_4807])).

tff(c_4817,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3666,c_4810])).

tff(c_4269,plain,(
    ! [A_233,B_234] :
      ( u1_pre_topc(k6_tmap_1(A_233,B_234)) = k5_tmap_1(A_233,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4278,plain,(
    ! [B_234] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_234)) = k5_tmap_1('#skF_1',B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_4269])).

tff(c_4288,plain,(
    ! [B_234] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_234)) = k5_tmap_1('#skF_1',B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4278])).

tff(c_4296,plain,(
    ! [B_235] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_235)) = k5_tmap_1('#skF_1',B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4288])).

tff(c_4304,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3541,c_4296])).

tff(c_3754,plain,(
    ! [A_221,B_222] :
      ( l1_pre_topc(k6_tmap_1(A_221,B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3757,plain,(
    ! [B_222] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_3754])).

tff(c_3763,plain,(
    ! [B_222] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3757])).

tff(c_3766,plain,(
    ! [B_223] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_223))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3763])).

tff(c_3774,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3541,c_3766])).

tff(c_3703,plain,(
    ! [A_214,B_215] :
      ( v1_pre_topc(k6_tmap_1(A_214,B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3706,plain,(
    ! [B_215] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_3703])).

tff(c_3712,plain,(
    ! [B_215] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3706])).

tff(c_3715,plain,(
    ! [B_216] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_216))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3712])).

tff(c_3723,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3541,c_3715])).

tff(c_4016,plain,(
    ! [A_230,B_231] :
      ( u1_struct_0(k6_tmap_1(A_230,B_231)) = u1_struct_0(A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4025,plain,(
    ! [B_231] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_231)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_231,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_4016])).

tff(c_4035,plain,(
    ! [B_231] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_231)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_231,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3540,c_4025])).

tff(c_4038,plain,(
    ! [B_232] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_232)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4035])).

tff(c_4046,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3541,c_4038])).

tff(c_4103,plain,
    ( g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4046,c_12])).

tff(c_4143,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3774,c_3723,c_4103])).

tff(c_4306,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4143])).

tff(c_4821,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4817,c_4306])).

tff(c_4824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3547,c_4821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.39  
% 6.62/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.39  %$ m2_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.62/2.39  
% 6.62/2.39  %Foreground sorts:
% 6.62/2.39  
% 6.62/2.39  
% 6.62/2.39  %Background operators:
% 6.62/2.39  
% 6.62/2.39  
% 6.62/2.39  %Foreground operators:
% 6.62/2.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.62/2.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.62/2.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.62/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.39  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.62/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.62/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.62/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.62/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.62/2.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.62/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.62/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.39  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 6.62/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.62/2.39  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 6.62/2.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.62/2.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.62/2.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.62/2.39  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 6.62/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.39  
% 6.92/2.42  tff(f_168, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 6.92/2.42  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.92/2.42  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.92/2.42  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 6.92/2.42  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 6.92/2.42  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.92/2.42  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.92/2.42  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 6.92/2.42  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 6.92/2.42  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.92/2.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.92/2.42  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.92/2.42  tff(f_125, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 6.92/2.42  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 6.92/2.42  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 6.92/2.42  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.92/2.42  tff(c_20, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.92/2.42  tff(c_77, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.92/2.42  tff(c_83, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_20, c_77])).
% 6.92/2.42  tff(c_87, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_83])).
% 6.92/2.42  tff(c_62, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.92/2.42  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 6.92/2.42  tff(c_100, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_82])).
% 6.92/2.42  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.92/2.42  tff(c_121, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_87, c_56])).
% 6.92/2.42  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.92/2.42  tff(c_88, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_48])).
% 6.92/2.42  tff(c_1827, plain, (![B_134, A_135]: (v3_pre_topc(B_134, A_135) | ~r2_hidden(B_134, u1_pre_topc(A_135)) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.92/2.42  tff(c_1830, plain, (![B_134]: (v3_pre_topc(B_134, '#skF_1') | ~r2_hidden(B_134, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1827])).
% 6.92/2.42  tff(c_1859, plain, (![B_138]: (v3_pre_topc(B_138, '#skF_1') | ~r2_hidden(B_138, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1830])).
% 6.92/2.42  tff(c_1862, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_1859])).
% 6.92/2.42  tff(c_1869, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_121, c_1862])).
% 6.92/2.42  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.92/2.42  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.92/2.42  tff(c_2866, plain, (![B_174, A_175]: (r2_hidden(B_174, u1_pre_topc(A_175)) | k5_tmap_1(A_175, B_174)!=u1_pre_topc(A_175) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.92/2.42  tff(c_2881, plain, (![B_174]: (r2_hidden(B_174, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_174)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_174, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2866])).
% 6.92/2.42  tff(c_2892, plain, (![B_174]: (r2_hidden(B_174, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_174)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_174, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2881])).
% 6.92/2.42  tff(c_3172, plain, (![B_186]: (r2_hidden(B_186, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_186)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2892])).
% 6.92/2.42  tff(c_3175, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_88, c_3172])).
% 6.92/2.42  tff(c_3182, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1869, c_3175])).
% 6.92/2.42  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.92/2.42  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.92/2.42  tff(c_63, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 6.92/2.42  tff(c_161, plain, (![B_52, A_53]: (r2_hidden(B_52, u1_pre_topc(A_53)) | ~v3_pre_topc(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.92/2.42  tff(c_173, plain, (![A_54]: (r2_hidden(u1_struct_0(A_54), u1_pre_topc(A_54)) | ~v3_pre_topc(u1_struct_0(A_54), A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_63, c_161])).
% 6.92/2.42  tff(c_176, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_173])).
% 6.92/2.42  tff(c_178, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_87, c_176])).
% 6.92/2.42  tff(c_179, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_178])).
% 6.92/2.42  tff(c_322, plain, (![A_74, B_75]: (m2_connsp_2(k2_struct_0(A_74), A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.92/2.42  tff(c_324, plain, (![B_75]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_322])).
% 6.92/2.42  tff(c_329, plain, (![B_75]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_324])).
% 6.92/2.42  tff(c_350, plain, (![B_77]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_329])).
% 6.92/2.42  tff(c_359, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_63, c_350])).
% 6.92/2.42  tff(c_1375, plain, (![B_109, A_110, C_111]: (r1_tarski(B_109, k1_tops_1(A_110, C_111)) | ~m2_connsp_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.92/2.42  tff(c_1387, plain, (![B_109, C_111]: (r1_tarski(B_109, k1_tops_1('#skF_1', C_111)) | ~m2_connsp_2(C_111, '#skF_1', B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1375])).
% 6.92/2.42  tff(c_1402, plain, (![B_112, C_113]: (r1_tarski(B_112, k1_tops_1('#skF_1', C_113)) | ~m2_connsp_2(C_113, '#skF_1', B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_87, c_1387])).
% 6.92/2.42  tff(c_1734, plain, (![B_123]: (r1_tarski(B_123, k1_tops_1('#skF_1', k2_struct_0('#skF_1'))) | ~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_63, c_1402])).
% 6.92/2.42  tff(c_122, plain, (![A_48, B_49]: (r1_tarski(k1_tops_1(A_48, B_49), B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.92/2.42  tff(c_131, plain, (![A_50]: (r1_tarski(k1_tops_1(A_50, u1_struct_0(A_50)), u1_struct_0(A_50)) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_63, c_122])).
% 6.92/2.42  tff(c_136, plain, (r1_tarski(k1_tops_1('#skF_1', k2_struct_0('#skF_1')), u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_131])).
% 6.92/2.42  tff(c_142, plain, (r1_tarski(k1_tops_1('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_87, c_136])).
% 6.92/2.42  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.92/2.42  tff(c_147, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_142, c_2])).
% 6.92/2.42  tff(c_190, plain, (~r1_tarski(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_147])).
% 6.92/2.42  tff(c_1739, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1734, c_190])).
% 6.92/2.42  tff(c_1748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_359, c_1739])).
% 6.92/2.42  tff(c_1749, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_147])).
% 6.92/2.42  tff(c_1780, plain, (![A_127, B_128]: (v3_pre_topc(k1_tops_1(A_127, B_128), A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.92/2.42  tff(c_1789, plain, (![A_129]: (v3_pre_topc(k1_tops_1(A_129, u1_struct_0(A_129)), A_129) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(resolution, [status(thm)], [c_63, c_1780])).
% 6.92/2.42  tff(c_1792, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_struct_0('#skF_1')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_1789])).
% 6.92/2.42  tff(c_1794, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1749, c_1792])).
% 6.92/2.42  tff(c_1796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_1794])).
% 6.92/2.42  tff(c_1797, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_178])).
% 6.92/2.42  tff(c_3137, plain, (![A_183, B_184]: (k5_tmap_1(A_183, B_184)=u1_pre_topc(A_183) | ~r2_hidden(B_184, u1_pre_topc(A_183)) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.92/2.42  tff(c_3152, plain, (![B_184]: (k5_tmap_1('#skF_1', B_184)=u1_pre_topc('#skF_1') | ~r2_hidden(B_184, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_3137])).
% 6.92/2.42  tff(c_3163, plain, (![B_184]: (k5_tmap_1('#skF_1', B_184)=u1_pre_topc('#skF_1') | ~r2_hidden(B_184, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3152])).
% 6.92/2.42  tff(c_3445, plain, (![B_193]: (k5_tmap_1('#skF_1', B_193)=u1_pre_topc('#skF_1') | ~r2_hidden(B_193, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_3163])).
% 6.92/2.42  tff(c_3452, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_63, c_3445])).
% 6.92/2.42  tff(c_3457, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1797, c_3452])).
% 6.92/2.42  tff(c_1873, plain, (![A_139, B_140]: (l1_pre_topc(k6_tmap_1(A_139, B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.92/2.42  tff(c_1876, plain, (![B_140]: (l1_pre_topc(k6_tmap_1('#skF_1', B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1873])).
% 6.92/2.42  tff(c_1882, plain, (![B_140]: (l1_pre_topc(k6_tmap_1('#skF_1', B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1876])).
% 6.92/2.42  tff(c_1885, plain, (![B_141]: (l1_pre_topc(k6_tmap_1('#skF_1', B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1882])).
% 6.92/2.42  tff(c_1894, plain, (l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_63, c_1885])).
% 6.92/2.42  tff(c_1903, plain, (![A_142, B_143]: (v1_pre_topc(k6_tmap_1(A_142, B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.92/2.42  tff(c_1906, plain, (![B_143]: (v1_pre_topc(k6_tmap_1('#skF_1', B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1903])).
% 6.92/2.42  tff(c_1912, plain, (![B_143]: (v1_pre_topc(k6_tmap_1('#skF_1', B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1906])).
% 6.92/2.42  tff(c_1977, plain, (![B_144]: (v1_pre_topc(k6_tmap_1('#skF_1', B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1912])).
% 6.92/2.42  tff(c_1986, plain, (v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_63, c_1977])).
% 6.92/2.42  tff(c_2329, plain, (![A_159, B_160]: (u1_struct_0(k6_tmap_1(A_159, B_160))=u1_struct_0(A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.92/2.42  tff(c_2341, plain, (![B_160]: (u1_struct_0(k6_tmap_1('#skF_1', B_160))=u1_struct_0('#skF_1') | ~m1_subset_1(B_160, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2329])).
% 6.92/2.42  tff(c_2351, plain, (![B_160]: (u1_struct_0(k6_tmap_1('#skF_1', B_160))=k2_struct_0('#skF_1') | ~m1_subset_1(B_160, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_87, c_2341])).
% 6.92/2.42  tff(c_2354, plain, (![B_161]: (u1_struct_0(k6_tmap_1('#skF_1', B_161))=k2_struct_0('#skF_1') | ~m1_subset_1(B_161, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2351])).
% 6.92/2.42  tff(c_2363, plain, (u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_63, c_2354])).
% 6.92/2.42  tff(c_2729, plain, (![A_168, B_169]: (u1_pre_topc(k6_tmap_1(A_168, B_169))=k5_tmap_1(A_168, B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.92/2.42  tff(c_2744, plain, (![B_169]: (u1_pre_topc(k6_tmap_1('#skF_1', B_169))=k5_tmap_1('#skF_1', B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2729])).
% 6.92/2.42  tff(c_2755, plain, (![B_169]: (u1_pre_topc(k6_tmap_1('#skF_1', B_169))=k5_tmap_1('#skF_1', B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2744])).
% 6.92/2.42  tff(c_2808, plain, (![B_173]: (u1_pre_topc(k6_tmap_1('#skF_1', B_173))=k5_tmap_1('#skF_1', B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2755])).
% 6.92/2.42  tff(c_2817, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_63, c_2808])).
% 6.92/2.42  tff(c_12, plain, (![A_5]: (g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))=A_5 | ~v1_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.92/2.42  tff(c_2847, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), k5_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1')) | ~v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2817, c_12])).
% 6.92/2.42  tff(c_2855, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_1986, c_2363, c_2847])).
% 6.92/2.42  tff(c_3458, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3457, c_2855])).
% 6.92/2.42  tff(c_3460, plain, (k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_3458])).
% 6.92/2.42  tff(c_3459, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3457, c_2817])).
% 6.92/2.42  tff(c_3485, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3460, c_3459])).
% 6.92/2.42  tff(c_2816, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_2808])).
% 6.92/2.42  tff(c_3531, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3485, c_2816])).
% 6.92/2.42  tff(c_3533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3182, c_3531])).
% 6.92/2.42  tff(c_3534, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 6.92/2.42  tff(c_3536, plain, (![A_194]: (u1_struct_0(A_194)=k2_struct_0(A_194) | ~l1_pre_topc(A_194))), inference(resolution, [status(thm)], [c_20, c_77])).
% 6.92/2.42  tff(c_3540, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3536])).
% 6.92/2.42  tff(c_3547, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_3540, c_56])).
% 6.92/2.42  tff(c_3541, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3540, c_48])).
% 6.92/2.42  tff(c_3638, plain, (![B_206, A_207]: (r2_hidden(B_206, u1_pre_topc(A_207)) | ~v3_pre_topc(B_206, A_207) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.92/2.42  tff(c_3641, plain, (![B_206]: (r2_hidden(B_206, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_206, '#skF_1') | ~m1_subset_1(B_206, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_3638])).
% 6.92/2.42  tff(c_3656, plain, (![B_209]: (r2_hidden(B_209, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_209, '#skF_1') | ~m1_subset_1(B_209, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3641])).
% 6.92/2.42  tff(c_3659, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3541, c_3656])).
% 6.92/2.42  tff(c_3666, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_3659])).
% 6.92/2.42  tff(c_4672, plain, (![A_251, B_252]: (k5_tmap_1(A_251, B_252)=u1_pre_topc(A_251) | ~r2_hidden(B_252, u1_pre_topc(A_251)) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.92/2.42  tff(c_4687, plain, (![B_252]: (k5_tmap_1('#skF_1', B_252)=u1_pre_topc('#skF_1') | ~r2_hidden(B_252, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_4672])).
% 6.92/2.42  tff(c_4698, plain, (![B_252]: (k5_tmap_1('#skF_1', B_252)=u1_pre_topc('#skF_1') | ~r2_hidden(B_252, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4687])).
% 6.92/2.42  tff(c_4807, plain, (![B_255]: (k5_tmap_1('#skF_1', B_255)=u1_pre_topc('#skF_1') | ~r2_hidden(B_255, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_4698])).
% 6.92/2.42  tff(c_4810, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3541, c_4807])).
% 6.92/2.42  tff(c_4817, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3666, c_4810])).
% 6.92/2.42  tff(c_4269, plain, (![A_233, B_234]: (u1_pre_topc(k6_tmap_1(A_233, B_234))=k5_tmap_1(A_233, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.92/2.42  tff(c_4278, plain, (![B_234]: (u1_pre_topc(k6_tmap_1('#skF_1', B_234))=k5_tmap_1('#skF_1', B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_4269])).
% 6.92/2.42  tff(c_4288, plain, (![B_234]: (u1_pre_topc(k6_tmap_1('#skF_1', B_234))=k5_tmap_1('#skF_1', B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4278])).
% 6.92/2.42  tff(c_4296, plain, (![B_235]: (u1_pre_topc(k6_tmap_1('#skF_1', B_235))=k5_tmap_1('#skF_1', B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_4288])).
% 6.92/2.42  tff(c_4304, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3541, c_4296])).
% 6.92/2.42  tff(c_3754, plain, (![A_221, B_222]: (l1_pre_topc(k6_tmap_1(A_221, B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.92/2.42  tff(c_3757, plain, (![B_222]: (l1_pre_topc(k6_tmap_1('#skF_1', B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_3754])).
% 6.92/2.42  tff(c_3763, plain, (![B_222]: (l1_pre_topc(k6_tmap_1('#skF_1', B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3757])).
% 6.92/2.42  tff(c_3766, plain, (![B_223]: (l1_pre_topc(k6_tmap_1('#skF_1', B_223)) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_3763])).
% 6.92/2.42  tff(c_3774, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3541, c_3766])).
% 6.92/2.42  tff(c_3703, plain, (![A_214, B_215]: (v1_pre_topc(k6_tmap_1(A_214, B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.92/2.42  tff(c_3706, plain, (![B_215]: (v1_pre_topc(k6_tmap_1('#skF_1', B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_3703])).
% 6.92/2.42  tff(c_3712, plain, (![B_215]: (v1_pre_topc(k6_tmap_1('#skF_1', B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3706])).
% 6.92/2.42  tff(c_3715, plain, (![B_216]: (v1_pre_topc(k6_tmap_1('#skF_1', B_216)) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_3712])).
% 6.92/2.42  tff(c_3723, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3541, c_3715])).
% 6.92/2.42  tff(c_4016, plain, (![A_230, B_231]: (u1_struct_0(k6_tmap_1(A_230, B_231))=u1_struct_0(A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.92/2.42  tff(c_4025, plain, (![B_231]: (u1_struct_0(k6_tmap_1('#skF_1', B_231))=u1_struct_0('#skF_1') | ~m1_subset_1(B_231, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_4016])).
% 6.92/2.42  tff(c_4035, plain, (![B_231]: (u1_struct_0(k6_tmap_1('#skF_1', B_231))=k2_struct_0('#skF_1') | ~m1_subset_1(B_231, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3540, c_4025])).
% 6.92/2.42  tff(c_4038, plain, (![B_232]: (u1_struct_0(k6_tmap_1('#skF_1', B_232))=k2_struct_0('#skF_1') | ~m1_subset_1(B_232, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_4035])).
% 6.92/2.42  tff(c_4046, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3541, c_4038])).
% 6.92/2.42  tff(c_4103, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4046, c_12])).
% 6.92/2.42  tff(c_4143, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3774, c_3723, c_4103])).
% 6.92/2.42  tff(c_4306, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4143])).
% 6.92/2.42  tff(c_4821, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4817, c_4306])).
% 6.92/2.42  tff(c_4824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3547, c_4821])).
% 6.92/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.42  
% 6.92/2.42  Inference rules
% 6.92/2.42  ----------------------
% 6.92/2.42  #Ref     : 0
% 6.92/2.42  #Sup     : 1067
% 6.92/2.42  #Fact    : 0
% 6.92/2.42  #Define  : 0
% 6.92/2.42  #Split   : 20
% 6.92/2.42  #Chain   : 0
% 6.92/2.42  #Close   : 0
% 6.92/2.42  
% 6.92/2.42  Ordering : KBO
% 6.92/2.42  
% 6.92/2.42  Simplification rules
% 6.92/2.42  ----------------------
% 6.92/2.42  #Subsume      : 44
% 6.92/2.42  #Demod        : 1547
% 6.92/2.42  #Tautology    : 362
% 6.92/2.42  #SimpNegUnit  : 102
% 6.92/2.42  #BackRed      : 48
% 6.92/2.42  
% 6.92/2.42  #Partial instantiations: 0
% 6.92/2.42  #Strategies tried      : 1
% 6.92/2.42  
% 6.92/2.42  Timing (in seconds)
% 6.92/2.42  ----------------------
% 6.92/2.42  Preprocessing        : 0.37
% 6.92/2.42  Parsing              : 0.20
% 6.92/2.42  CNF conversion       : 0.03
% 6.92/2.42  Main loop            : 1.24
% 6.92/2.43  Inferencing          : 0.39
% 6.92/2.43  Reduction            : 0.48
% 6.92/2.43  Demodulation         : 0.34
% 6.92/2.43  BG Simplification    : 0.05
% 6.92/2.43  Subsumption          : 0.23
% 6.92/2.43  Abstraction          : 0.05
% 6.92/2.43  MUC search           : 0.00
% 6.92/2.43  Cooper               : 0.00
% 6.92/2.43  Total                : 1.67
% 6.92/2.43  Index Insertion      : 0.00
% 6.92/2.43  Index Deletion       : 0.00
% 6.92/2.43  Index Matching       : 0.00
% 6.92/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
