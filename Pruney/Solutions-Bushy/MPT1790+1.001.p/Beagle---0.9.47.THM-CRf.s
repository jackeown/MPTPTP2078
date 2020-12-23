%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1790+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:23 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 251 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  156 ( 791 expanded)
%              Number of equality atoms :   31 ( 141 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
               => ( C = B
                 => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_37,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_191,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,k5_tmap_1(A_51,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_195,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_191])).

tff(c_201,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_195])).

tff(c_202,plain,(
    r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_201])).

tff(c_24,plain,(
    ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_39,plain,(
    ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_71,plain,(
    ! [B_34,A_35] :
      ( v3_pre_topc(B_34,A_35)
      | ~ r2_hidden(B_34,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_74])).

tff(c_85,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_110,plain,(
    ! [A_40,B_41] :
      ( l1_pre_topc(k6_tmap_1(A_40,B_41))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_116,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_110])).

tff(c_122,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_116])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_85,c_122])).

tff(c_126,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_156,plain,(
    ! [A_46,B_47] :
      ( v1_pre_topc(k6_tmap_1(A_46,B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_162,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_156])).

tff(c_168,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_162])).

tff(c_169,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_168])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k5_tmap_1(A_8,B_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_231,plain,(
    ! [A_63,B_64] :
      ( g1_pre_topc(u1_struct_0(A_63),k5_tmap_1(A_63,B_64)) = k6_tmap_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_235,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_3')) = k6_tmap_1('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_231])).

tff(c_241,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_3')) = k6_tmap_1('#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_235])).

tff(c_242,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_3')) = k6_tmap_1('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_241])).

tff(c_20,plain,(
    ! [C_16,A_12,D_17,B_13] :
      ( C_16 = A_12
      | g1_pre_topc(C_16,D_17) != g1_pre_topc(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_253,plain,(
    ! [C_16,D_17] :
      ( u1_struct_0('#skF_1') = C_16
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(C_16,D_17)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_20])).

tff(c_271,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_274,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_271])).

tff(c_277,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_37,c_274])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_277])).

tff(c_307,plain,(
    ! [C_72,D_73] :
      ( u1_struct_0('#skF_1') = C_72
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(C_72,D_73) ) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_317,plain,(
    ! [A_74] :
      ( u1_struct_0(A_74) = u1_struct_0('#skF_1')
      | k6_tmap_1('#skF_1','#skF_3') != A_74
      | ~ v1_pre_topc(A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_307])).

tff(c_320,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_3')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_169,c_317])).

tff(c_323,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_3')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_320])).

tff(c_362,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) = k6_tmap_1('#skF_1','#skF_3')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_2])).

tff(c_382,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) = k6_tmap_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_169,c_362])).

tff(c_281,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_18,plain,(
    ! [D_17,B_13,C_16,A_12] :
      ( D_17 = B_13
      | g1_pre_topc(C_16,D_17) != g1_pre_topc(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_257,plain,(
    ! [D_17,C_16] :
      ( k5_tmap_1('#skF_1','#skF_3') = D_17
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(C_16,D_17)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_18])).

tff(c_325,plain,(
    ! [D_17,C_16] :
      ( k5_tmap_1('#skF_1','#skF_3') = D_17
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(C_16,D_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_257])).

tff(c_409,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = k5_tmap_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_325])).

tff(c_125,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_414,plain,(
    ~ r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_125])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_414])).

%------------------------------------------------------------------------------
