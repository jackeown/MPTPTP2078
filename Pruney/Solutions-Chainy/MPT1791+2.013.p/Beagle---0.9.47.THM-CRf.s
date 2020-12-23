%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 682 expanded)
%              Number of leaves         :   32 ( 253 expanded)
%              Depth                    :   16
%              Number of atoms          :  396 (2161 expanded)
%              Number of equality atoms :   58 ( 324 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_62,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_87,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_109,plain,(
    ! [B_56,A_57] :
      ( v3_pre_topc(B_56,A_57)
      | ~ r2_hidden(B_56,u1_pre_topc(A_57))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_109])).

tff(c_119,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_115])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_119])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_167,plain,(
    ! [B_74,A_75] :
      ( v1_tops_2(B_74,A_75)
      | ~ r1_tarski(B_74,u1_pre_topc(A_75))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75))))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_170,plain,(
    ! [A_9] :
      ( v1_tops_2(u1_pre_topc(A_9),A_9)
      | ~ r1_tarski(u1_pre_topc(A_9),u1_pre_topc(A_9))
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_173,plain,(
    ! [A_9] :
      ( v1_tops_2(u1_pre_topc(A_9),A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_1321,plain,(
    ! [A_137,B_138] :
      ( u1_pre_topc(k6_tmap_1(A_137,B_138)) = k5_tmap_1(A_137,B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1330,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1321])).

tff(c_1336,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1330])).

tff(c_1337,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1336])).

tff(c_291,plain,(
    ! [A_89,B_90] :
      ( u1_pre_topc(k6_tmap_1(A_89,B_90)) = k5_tmap_1(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_300,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_291])).

tff(c_306,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_300])).

tff(c_307,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_306])).

tff(c_135,plain,(
    ! [A_64,B_65] :
      ( l1_pre_topc(k6_tmap_1(A_64,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_141,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_145,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_141])).

tff(c_146,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_145])).

tff(c_198,plain,(
    ! [A_86,B_87] :
      ( u1_struct_0(k6_tmap_1(A_86,B_87)) = u1_struct_0(A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_204,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_198])).

tff(c_208,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_204])).

tff(c_209,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_208])).

tff(c_241,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_14])).

tff(c_265,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_241])).

tff(c_26,plain,(
    ! [B_22,A_20] :
      ( r1_tarski(B_22,u1_pre_topc(A_20))
      | ~ v1_tops_2(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20))))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_274,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_265,c_26])).

tff(c_285,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_274])).

tff(c_288,plain,(
    ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_309,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_288])).

tff(c_318,plain,
    ( v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_173])).

tff(c_339,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_318])).

tff(c_333,plain,
    ( m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_14])).

tff(c_349,plain,(
    m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_209,c_333])).

tff(c_68,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_88,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_68])).

tff(c_1258,plain,(
    ! [B_134,A_135] :
      ( v1_tops_2(B_134,A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135))))))
      | ~ v1_tops_2(B_134,g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1276,plain,(
    ! [B_134] :
      ( v1_tops_2(B_134,'#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_tops_2(B_134,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1258])).

tff(c_1291,plain,(
    ! [B_134] :
      ( v1_tops_2(B_134,'#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_134,k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_88,c_209,c_1276])).

tff(c_1294,plain,(
    ! [B_136] :
      ( v1_tops_2(B_136,'#skF_2')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_136,k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1291])).

tff(c_1300,plain,
    ( v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_349,c_1294])).

tff(c_1308,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_1300])).

tff(c_1310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_1308])).

tff(c_1311,plain,(
    r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1315,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1311,c_2])).

tff(c_1319,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_1338,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1319])).

tff(c_226,plain,(
    ! [B_22] :
      ( r1_tarski(B_22,u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_tops_2(B_22,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_26])).

tff(c_255,plain,(
    ! [B_22] :
      ( r1_tarski(B_22,u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_tops_2(B_22,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_226])).

tff(c_1748,plain,(
    ! [B_163] :
      ( r1_tarski(B_163,k5_tmap_1('#skF_2','#skF_3'))
      | ~ v1_tops_2(B_163,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_255])).

tff(c_1755,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),k5_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1748])).

tff(c_1761,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),k5_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1755])).

tff(c_1762,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1338,c_1761])).

tff(c_1953,plain,(
    ! [B_173,A_174] :
      ( v1_tops_2(B_173,g1_pre_topc(u1_struct_0(A_174),u1_pre_topc(A_174)))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_174))))
      | ~ v1_tops_2(B_173,A_174)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1962,plain,(
    ! [B_173] :
      ( v1_tops_2(B_173,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_173,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1953])).

tff(c_1968,plain,(
    ! [B_173] :
      ( v1_tops_2(B_173,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_173,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1962])).

tff(c_2065,plain,(
    ! [B_175] :
      ( v1_tops_2(B_175,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_175,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1968])).

tff(c_2072,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_2065])).

tff(c_2078,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2072])).

tff(c_2079,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1762,c_2078])).

tff(c_2142,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_173,c_2079])).

tff(c_2146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2142])).

tff(c_2147,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_2194,plain,(
    ! [A_176,B_177] :
      ( u1_pre_topc(k6_tmap_1(A_176,B_177)) = k5_tmap_1(A_176,B_177)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2203,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2194])).

tff(c_2209,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2147,c_2203])).

tff(c_2210,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2209])).

tff(c_174,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(B_76,k5_tmap_1(A_77,B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_178,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_174])).

tff(c_182,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_178])).

tff(c_183,plain,(
    r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_182])).

tff(c_2212,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_183])).

tff(c_2214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2212])).

tff(c_2215,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2216,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2236,plain,(
    ! [B_187,A_188] :
      ( r2_hidden(B_187,u1_pre_topc(A_188))
      | ~ v3_pre_topc(B_187,A_188)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2242,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2236])).

tff(c_2246,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2216,c_2242])).

tff(c_3059,plain,(
    ! [A_240,B_241] :
      ( k5_tmap_1(A_240,B_241) = u1_pre_topc(A_240)
      | ~ r2_hidden(B_241,u1_pre_topc(A_240))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3074,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3059])).

tff(c_3085,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2246,c_3074])).

tff(c_3086,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3085])).

tff(c_2900,plain,(
    ! [A_237,B_238] :
      ( u1_pre_topc(k6_tmap_1(A_237,B_238)) = k5_tmap_1(A_237,B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2912,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2900])).

tff(c_2919,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2912])).

tff(c_2920,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2919])).

tff(c_2720,plain,(
    ! [A_228,B_229] :
      ( k5_tmap_1(A_228,B_229) = u1_pre_topc(A_228)
      | ~ r2_hidden(B_229,u1_pre_topc(A_228))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2735,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2720])).

tff(c_2746,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2246,c_2735])).

tff(c_2747,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2746])).

tff(c_2562,plain,(
    ! [A_225,B_226] :
      ( u1_pre_topc(k6_tmap_1(A_225,B_226)) = k5_tmap_1(A_225,B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2574,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2562])).

tff(c_2581,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2574])).

tff(c_2582,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2581])).

tff(c_2247,plain,(
    ! [A_189,B_190] :
      ( l1_pre_topc(k6_tmap_1(A_189,B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2253,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2247])).

tff(c_2257,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2253])).

tff(c_2258,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2257])).

tff(c_2354,plain,(
    ! [A_216,B_217] :
      ( u1_struct_0(k6_tmap_1(A_216,B_217)) = u1_struct_0(A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2360,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2354])).

tff(c_2364,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2360])).

tff(c_2365,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2364])).

tff(c_2397,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2365,c_14])).

tff(c_2421,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_2397])).

tff(c_2430,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2421,c_26])).

tff(c_2441,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2430])).

tff(c_2445,plain,(
    ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2441])).

tff(c_24,plain,(
    ! [B_22,A_20] :
      ( v1_tops_2(B_22,A_20)
      | ~ r1_tarski(B_22,u1_pre_topc(A_20))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20))))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2427,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2421,c_24])).

tff(c_2438,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2427])).

tff(c_2446,plain,(
    ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_2445,c_2438])).

tff(c_2585,plain,(
    ~ r1_tarski(k5_tmap_1('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_2446])).

tff(c_2753,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2747,c_2585])).

tff(c_2760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2753])).

tff(c_2761,plain,(
    r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2441])).

tff(c_2765,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2761,c_2])).

tff(c_2769,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2765])).

tff(c_2925,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2769])).

tff(c_3089,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3086,c_2925])).

tff(c_3098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3089])).

tff(c_3099,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2765])).

tff(c_3280,plain,(
    ! [A_250,B_251] :
      ( u1_pre_topc(k6_tmap_1(A_250,B_251)) = k5_tmap_1(A_250,B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3295,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3280])).

tff(c_3306,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3099,c_3295])).

tff(c_3307,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3306])).

tff(c_3518,plain,(
    ! [A_272,B_273] :
      ( g1_pre_topc(u1_struct_0(A_272),k5_tmap_1(A_272,B_273)) = k6_tmap_1(A_272,B_273)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3528,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3518])).

tff(c_3539,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3307,c_3528])).

tff(c_3541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2215,c_3539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/2.06  
% 4.95/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/2.06  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.95/2.06  
% 4.95/2.06  %Foreground sorts:
% 4.95/2.06  
% 4.95/2.06  
% 4.95/2.06  %Background operators:
% 4.95/2.06  
% 4.95/2.06  
% 4.95/2.06  %Foreground operators:
% 4.95/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.95/2.06  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.95/2.06  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.95/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/2.06  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.95/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/2.06  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.95/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.95/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/2.06  tff('#skF_2', type, '#skF_2': $i).
% 4.95/2.06  tff('#skF_3', type, '#skF_3': $i).
% 4.95/2.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.95/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.95/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/2.06  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 4.95/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.95/2.06  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 4.95/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.95/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.95/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.95/2.06  
% 5.29/2.09  tff(f_171, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 5.29/2.09  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.29/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.29/2.09  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.29/2.09  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 5.29/2.09  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 5.29/2.09  tff(f_116, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 5.29/2.09  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_compts_1)).
% 5.29/2.09  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 5.29/2.09  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 5.29/2.09  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 5.29/2.09  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.29/2.09  tff(c_62, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.29/2.09  tff(c_87, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 5.29/2.09  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.29/2.09  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.29/2.09  tff(c_109, plain, (![B_56, A_57]: (v3_pre_topc(B_56, A_57) | ~r2_hidden(B_56, u1_pre_topc(A_57)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.29/2.09  tff(c_115, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_109])).
% 5.29/2.09  tff(c_119, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_115])).
% 5.29/2.09  tff(c_120, plain, (~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_87, c_119])).
% 5.29/2.09  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.29/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.29/2.09  tff(c_14, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/2.09  tff(c_167, plain, (![B_74, A_75]: (v1_tops_2(B_74, A_75) | ~r1_tarski(B_74, u1_pre_topc(A_75)) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75)))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.29/2.09  tff(c_170, plain, (![A_9]: (v1_tops_2(u1_pre_topc(A_9), A_9) | ~r1_tarski(u1_pre_topc(A_9), u1_pre_topc(A_9)) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_14, c_167])).
% 5.29/2.09  tff(c_173, plain, (![A_9]: (v1_tops_2(u1_pre_topc(A_9), A_9) | ~l1_pre_topc(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_170])).
% 5.29/2.09  tff(c_1321, plain, (![A_137, B_138]: (u1_pre_topc(k6_tmap_1(A_137, B_138))=k5_tmap_1(A_137, B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_1330, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1321])).
% 5.29/2.09  tff(c_1336, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1330])).
% 5.29/2.09  tff(c_1337, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1336])).
% 5.29/2.09  tff(c_291, plain, (![A_89, B_90]: (u1_pre_topc(k6_tmap_1(A_89, B_90))=k5_tmap_1(A_89, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_300, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_291])).
% 5.29/2.09  tff(c_306, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_300])).
% 5.29/2.09  tff(c_307, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_306])).
% 5.29/2.09  tff(c_135, plain, (![A_64, B_65]: (l1_pre_topc(k6_tmap_1(A_64, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.29/2.09  tff(c_141, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_135])).
% 5.29/2.09  tff(c_145, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_141])).
% 5.29/2.09  tff(c_146, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_145])).
% 5.29/2.09  tff(c_198, plain, (![A_86, B_87]: (u1_struct_0(k6_tmap_1(A_86, B_87))=u1_struct_0(A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_204, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_198])).
% 5.29/2.09  tff(c_208, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_204])).
% 5.29/2.09  tff(c_209, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_208])).
% 5.29/2.09  tff(c_241, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_14])).
% 5.29/2.09  tff(c_265, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_241])).
% 5.29/2.09  tff(c_26, plain, (![B_22, A_20]: (r1_tarski(B_22, u1_pre_topc(A_20)) | ~v1_tops_2(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20)))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.29/2.09  tff(c_274, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_265, c_26])).
% 5.29/2.09  tff(c_285, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_274])).
% 5.29/2.09  tff(c_288, plain, (~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_285])).
% 5.29/2.09  tff(c_309, plain, (~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_288])).
% 5.29/2.09  tff(c_318, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_173])).
% 5.29/2.09  tff(c_339, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_318])).
% 5.29/2.09  tff(c_333, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_14])).
% 5.29/2.09  tff(c_349, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_209, c_333])).
% 5.29/2.09  tff(c_68, plain, (v3_pre_topc('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.29/2.09  tff(c_88, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_87, c_68])).
% 5.29/2.09  tff(c_1258, plain, (![B_134, A_135]: (v1_tops_2(B_134, A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135)))))) | ~v1_tops_2(B_134, g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.29/2.09  tff(c_1276, plain, (![B_134]: (v1_tops_2(B_134, '#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_tops_2(B_134, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1258])).
% 5.29/2.09  tff(c_1291, plain, (![B_134]: (v1_tops_2(B_134, '#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_134, k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_88, c_209, c_1276])).
% 5.29/2.09  tff(c_1294, plain, (![B_136]: (v1_tops_2(B_136, '#skF_2') | ~m1_subset_1(B_136, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_136, k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1291])).
% 5.29/2.09  tff(c_1300, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_349, c_1294])).
% 5.29/2.09  tff(c_1308, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_1300])).
% 5.29/2.09  tff(c_1310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_1308])).
% 5.29/2.09  tff(c_1311, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_285])).
% 5.29/2.09  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.29/2.09  tff(c_1315, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_1311, c_2])).
% 5.29/2.09  tff(c_1319, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1315])).
% 5.29/2.09  tff(c_1338, plain, (~r1_tarski(u1_pre_topc('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1319])).
% 5.29/2.09  tff(c_226, plain, (![B_22]: (r1_tarski(B_22, u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_tops_2(B_22, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_209, c_26])).
% 5.29/2.09  tff(c_255, plain, (![B_22]: (r1_tarski(B_22, u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_tops_2(B_22, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_226])).
% 5.29/2.09  tff(c_1748, plain, (![B_163]: (r1_tarski(B_163, k5_tmap_1('#skF_2', '#skF_3')) | ~v1_tops_2(B_163, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_163, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_255])).
% 5.29/2.09  tff(c_1755, plain, (r1_tarski(u1_pre_topc('#skF_2'), k5_tmap_1('#skF_2', '#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1748])).
% 5.29/2.09  tff(c_1761, plain, (r1_tarski(u1_pre_topc('#skF_2'), k5_tmap_1('#skF_2', '#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1755])).
% 5.29/2.09  tff(c_1762, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1338, c_1761])).
% 5.29/2.09  tff(c_1953, plain, (![B_173, A_174]: (v1_tops_2(B_173, g1_pre_topc(u1_struct_0(A_174), u1_pre_topc(A_174))) | ~m1_subset_1(B_173, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_174)))) | ~v1_tops_2(B_173, A_174) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.29/2.09  tff(c_1962, plain, (![B_173]: (v1_tops_2(B_173, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_173, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_173, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1953])).
% 5.29/2.09  tff(c_1968, plain, (![B_173]: (v1_tops_2(B_173, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_173, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_173, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1962])).
% 5.29/2.09  tff(c_2065, plain, (![B_175]: (v1_tops_2(B_175, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_175, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_175, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1968])).
% 5.29/2.09  tff(c_2072, plain, (v1_tops_2(u1_pre_topc('#skF_2'), k6_tmap_1('#skF_2', '#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_2065])).
% 5.29/2.09  tff(c_2078, plain, (v1_tops_2(u1_pre_topc('#skF_2'), k6_tmap_1('#skF_2', '#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2072])).
% 5.29/2.09  tff(c_2079, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1762, c_2078])).
% 5.29/2.09  tff(c_2142, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_173, c_2079])).
% 5.29/2.09  tff(c_2146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2142])).
% 5.29/2.09  tff(c_2147, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_1315])).
% 5.29/2.09  tff(c_2194, plain, (![A_176, B_177]: (u1_pre_topc(k6_tmap_1(A_176, B_177))=k5_tmap_1(A_176, B_177) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_2203, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2194])).
% 5.29/2.09  tff(c_2209, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2147, c_2203])).
% 5.29/2.09  tff(c_2210, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_2209])).
% 5.29/2.09  tff(c_174, plain, (![B_76, A_77]: (r2_hidden(B_76, k5_tmap_1(A_77, B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.29/2.09  tff(c_178, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_174])).
% 5.29/2.09  tff(c_182, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_178])).
% 5.29/2.09  tff(c_183, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_182])).
% 5.29/2.09  tff(c_2212, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_183])).
% 5.29/2.09  tff(c_2214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_2212])).
% 5.29/2.09  tff(c_2215, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 5.29/2.09  tff(c_2216, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 5.29/2.09  tff(c_2236, plain, (![B_187, A_188]: (r2_hidden(B_187, u1_pre_topc(A_188)) | ~v3_pre_topc(B_187, A_188) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.29/2.09  tff(c_2242, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2236])).
% 5.29/2.09  tff(c_2246, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2216, c_2242])).
% 5.29/2.09  tff(c_3059, plain, (![A_240, B_241]: (k5_tmap_1(A_240, B_241)=u1_pre_topc(A_240) | ~r2_hidden(B_241, u1_pre_topc(A_240)) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.29/2.09  tff(c_3074, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_3059])).
% 5.29/2.09  tff(c_3085, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2246, c_3074])).
% 5.29/2.09  tff(c_3086, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_3085])).
% 5.29/2.09  tff(c_2900, plain, (![A_237, B_238]: (u1_pre_topc(k6_tmap_1(A_237, B_238))=k5_tmap_1(A_237, B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237) | v2_struct_0(A_237))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_2912, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2900])).
% 5.29/2.09  tff(c_2919, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2912])).
% 5.29/2.09  tff(c_2920, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_2919])).
% 5.29/2.09  tff(c_2720, plain, (![A_228, B_229]: (k5_tmap_1(A_228, B_229)=u1_pre_topc(A_228) | ~r2_hidden(B_229, u1_pre_topc(A_228)) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.29/2.09  tff(c_2735, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2720])).
% 5.29/2.09  tff(c_2746, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2246, c_2735])).
% 5.29/2.09  tff(c_2747, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_2746])).
% 5.29/2.09  tff(c_2562, plain, (![A_225, B_226]: (u1_pre_topc(k6_tmap_1(A_225, B_226))=k5_tmap_1(A_225, B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_2574, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2562])).
% 5.29/2.09  tff(c_2581, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2574])).
% 5.29/2.09  tff(c_2582, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_2581])).
% 5.29/2.09  tff(c_2247, plain, (![A_189, B_190]: (l1_pre_topc(k6_tmap_1(A_189, B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.29/2.09  tff(c_2253, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2247])).
% 5.29/2.09  tff(c_2257, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2253])).
% 5.29/2.09  tff(c_2258, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2257])).
% 5.29/2.09  tff(c_2354, plain, (![A_216, B_217]: (u1_struct_0(k6_tmap_1(A_216, B_217))=u1_struct_0(A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_2360, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2354])).
% 5.29/2.09  tff(c_2364, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2360])).
% 5.29/2.09  tff(c_2365, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_2364])).
% 5.29/2.09  tff(c_2397, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2365, c_14])).
% 5.29/2.09  tff(c_2421, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2258, c_2397])).
% 5.29/2.09  tff(c_2430, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2421, c_26])).
% 5.29/2.09  tff(c_2441, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2430])).
% 5.29/2.09  tff(c_2445, plain, (~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_2441])).
% 5.29/2.09  tff(c_24, plain, (![B_22, A_20]: (v1_tops_2(B_22, A_20) | ~r1_tarski(B_22, u1_pre_topc(A_20)) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20)))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.29/2.09  tff(c_2427, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2') | ~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2421, c_24])).
% 5.29/2.09  tff(c_2438, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), '#skF_2') | ~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2427])).
% 5.29/2.09  tff(c_2446, plain, (~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_2445, c_2438])).
% 5.29/2.09  tff(c_2585, plain, (~r1_tarski(k5_tmap_1('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_2446])).
% 5.29/2.09  tff(c_2753, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2747, c_2585])).
% 5.29/2.09  tff(c_2760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2753])).
% 5.29/2.09  tff(c_2761, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_2441])).
% 5.29/2.09  tff(c_2765, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_2761, c_2])).
% 5.29/2.09  tff(c_2769, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2765])).
% 5.29/2.09  tff(c_2925, plain, (~r1_tarski(u1_pre_topc('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2769])).
% 5.29/2.09  tff(c_3089, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3086, c_2925])).
% 5.29/2.09  tff(c_3098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3089])).
% 5.29/2.09  tff(c_3099, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_2765])).
% 5.29/2.09  tff(c_3280, plain, (![A_250, B_251]: (u1_pre_topc(k6_tmap_1(A_250, B_251))=k5_tmap_1(A_250, B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.29/2.09  tff(c_3295, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_3280])).
% 5.29/2.09  tff(c_3306, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3099, c_3295])).
% 5.29/2.09  tff(c_3307, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_3306])).
% 5.29/2.09  tff(c_3518, plain, (![A_272, B_273]: (g1_pre_topc(u1_struct_0(A_272), k5_tmap_1(A_272, B_273))=k6_tmap_1(A_272, B_273) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.29/2.09  tff(c_3528, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_3518])).
% 5.29/2.09  tff(c_3539, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3307, c_3528])).
% 5.29/2.09  tff(c_3541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2215, c_3539])).
% 5.29/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.09  
% 5.29/2.09  Inference rules
% 5.29/2.09  ----------------------
% 5.29/2.09  #Ref     : 0
% 5.29/2.09  #Sup     : 634
% 5.29/2.09  #Fact    : 0
% 5.29/2.09  #Define  : 0
% 5.29/2.09  #Split   : 18
% 5.29/2.09  #Chain   : 0
% 5.29/2.09  #Close   : 0
% 5.29/2.09  
% 5.29/2.09  Ordering : KBO
% 5.29/2.09  
% 5.29/2.09  Simplification rules
% 5.29/2.09  ----------------------
% 5.29/2.09  #Subsume      : 71
% 5.29/2.09  #Demod        : 1049
% 5.29/2.09  #Tautology    : 238
% 5.29/2.09  #SimpNegUnit  : 152
% 5.29/2.09  #BackRed      : 56
% 5.29/2.09  
% 5.29/2.09  #Partial instantiations: 0
% 5.29/2.09  #Strategies tried      : 1
% 5.29/2.09  
% 5.29/2.09  Timing (in seconds)
% 5.29/2.09  ----------------------
% 5.29/2.09  Preprocessing        : 0.42
% 5.29/2.09  Parsing              : 0.22
% 5.29/2.09  CNF conversion       : 0.03
% 5.29/2.09  Main loop            : 0.79
% 5.29/2.09  Inferencing          : 0.25
% 5.29/2.09  Reduction            : 0.30
% 5.29/2.09  Demodulation         : 0.21
% 5.29/2.09  BG Simplification    : 0.04
% 5.29/2.09  Subsumption          : 0.14
% 5.29/2.09  Abstraction          : 0.04
% 5.29/2.09  MUC search           : 0.00
% 5.29/2.09  Cooper               : 0.00
% 5.29/2.09  Total                : 1.27
% 5.29/2.09  Index Insertion      : 0.00
% 5.29/2.09  Index Deletion       : 0.00
% 5.29/2.09  Index Matching       : 0.00
% 5.29/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
