%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:52 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 135 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 373 expanded)
%              Number of equality atoms :   38 (  88 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_63,plain,(
    ! [B_29,A_30] :
      ( v3_pre_topc(B_29,A_30)
      | ~ r2_hidden(B_29,u1_pre_topc(A_30))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_69,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_69])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_84,plain,(
    ! [B_35,A_36] :
      ( r2_hidden(B_35,u1_pre_topc(A_36))
      | k5_tmap_1(A_36,B_35) != u1_pre_topc(A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_90,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_87])).

tff(c_91,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_70,c_90])).

tff(c_146,plain,(
    ! [A_43,B_44] :
      ( g1_pre_topc(u1_struct_0(A_43),k5_tmap_1(A_43,B_44)) = k6_tmap_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_146])).

tff(c_151,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_148])).

tff(c_152,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_151])).

tff(c_6,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_35,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32])).

tff(c_58,plain,(
    ! [C_25,A_26,D_27,B_28] :
      ( C_25 = A_26
      | g1_pre_topc(C_25,D_27) != g1_pre_topc(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [C_25,D_27] :
      ( u1_struct_0('#skF_1') = C_25
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_25,D_27)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_58])).

tff(c_108,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_117,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_44,plain,(
    ! [D_19,B_20,C_21,A_22] :
      ( D_19 = B_20
      | g1_pre_topc(C_21,D_19) != g1_pre_topc(A_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_1') = D_19
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_21,D_19)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_44])).

tff(c_139,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_1') = D_19
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_21,D_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_48])).

tff(c_164,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_139])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_164])).

tff(c_182,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_183,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_196,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,u1_pre_topc(A_56))
      | ~ v3_pre_topc(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_199,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_196])).

tff(c_202,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_183,c_199])).

tff(c_250,plain,(
    ! [A_69,B_70] :
      ( k5_tmap_1(A_69,B_70) = u1_pre_topc(A_69)
      | ~ r2_hidden(B_70,u1_pre_topc(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_253,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_250])).

tff(c_256,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_202,c_253])).

tff(c_257,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_256])).

tff(c_210,plain,(
    ! [A_59,B_60] :
      ( g1_pre_topc(u1_struct_0(A_59),k5_tmap_1(A_59,B_60)) = k6_tmap_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_212,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_210])).

tff(c_215,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_212])).

tff(c_216,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_215])).

tff(c_261,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_216])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.37  
% 2.26/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.38  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.26/1.38  
% 2.26/1.38  %Foreground sorts:
% 2.26/1.38  
% 2.26/1.38  
% 2.26/1.38  %Background operators:
% 2.26/1.38  
% 2.26/1.38  
% 2.26/1.38  %Foreground operators:
% 2.26/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.26/1.38  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.26/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.26/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.38  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.26/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.26/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.38  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.26/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.26/1.38  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.26/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.38  
% 2.40/1.40  tff(f_88, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.40/1.40  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.40/1.40  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.40/1.40  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.40/1.40  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.40/1.40  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.40/1.40  tff(c_24, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.40/1.40  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.40/1.40  tff(c_34, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.40/1.40  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.40/1.40  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.40/1.40  tff(c_63, plain, (![B_29, A_30]: (v3_pre_topc(B_29, A_30) | ~r2_hidden(B_29, u1_pre_topc(A_30)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.40/1.40  tff(c_66, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.40/1.40  tff(c_69, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66])).
% 2.40/1.40  tff(c_70, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_34, c_69])).
% 2.40/1.40  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.40/1.40  tff(c_84, plain, (![B_35, A_36]: (r2_hidden(B_35, u1_pre_topc(A_36)) | k5_tmap_1(A_36, B_35)!=u1_pre_topc(A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.40  tff(c_87, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_84])).
% 2.40/1.40  tff(c_90, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_87])).
% 2.40/1.40  tff(c_91, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_70, c_90])).
% 2.40/1.40  tff(c_146, plain, (![A_43, B_44]: (g1_pre_topc(u1_struct_0(A_43), k5_tmap_1(A_43, B_44))=k6_tmap_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.40  tff(c_148, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_146])).
% 2.40/1.40  tff(c_151, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_148])).
% 2.40/1.40  tff(c_152, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_151])).
% 2.40/1.40  tff(c_6, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.40  tff(c_32, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.40/1.40  tff(c_35, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_32])).
% 2.40/1.40  tff(c_58, plain, (![C_25, A_26, D_27, B_28]: (C_25=A_26 | g1_pre_topc(C_25, D_27)!=g1_pre_topc(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.40  tff(c_62, plain, (![C_25, D_27]: (u1_struct_0('#skF_1')=C_25 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_25, D_27) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_35, c_58])).
% 2.40/1.40  tff(c_108, plain, (~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_62])).
% 2.40/1.40  tff(c_111, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_108])).
% 2.40/1.40  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_111])).
% 2.40/1.40  tff(c_117, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_62])).
% 2.40/1.40  tff(c_44, plain, (![D_19, B_20, C_21, A_22]: (D_19=B_20 | g1_pre_topc(C_21, D_19)!=g1_pre_topc(A_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.40  tff(c_48, plain, (![D_19, C_21]: (u1_pre_topc('#skF_1')=D_19 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_21, D_19) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_35, c_44])).
% 2.40/1.40  tff(c_139, plain, (![D_19, C_21]: (u1_pre_topc('#skF_1')=D_19 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_21, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_48])).
% 2.40/1.40  tff(c_164, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_152, c_139])).
% 2.40/1.40  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_164])).
% 2.40/1.40  tff(c_182, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.40/1.40  tff(c_183, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.40/1.40  tff(c_196, plain, (![B_55, A_56]: (r2_hidden(B_55, u1_pre_topc(A_56)) | ~v3_pre_topc(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.40/1.40  tff(c_199, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_196])).
% 2.40/1.40  tff(c_202, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_183, c_199])).
% 2.40/1.40  tff(c_250, plain, (![A_69, B_70]: (k5_tmap_1(A_69, B_70)=u1_pre_topc(A_69) | ~r2_hidden(B_70, u1_pre_topc(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.40  tff(c_253, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_250])).
% 2.40/1.40  tff(c_256, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_202, c_253])).
% 2.40/1.40  tff(c_257, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_256])).
% 2.40/1.40  tff(c_210, plain, (![A_59, B_60]: (g1_pre_topc(u1_struct_0(A_59), k5_tmap_1(A_59, B_60))=k6_tmap_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.40  tff(c_212, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_210])).
% 2.40/1.40  tff(c_215, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_212])).
% 2.40/1.40  tff(c_216, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_215])).
% 2.40/1.40  tff(c_261, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_216])).
% 2.40/1.40  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_261])).
% 2.40/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.40  
% 2.40/1.40  Inference rules
% 2.40/1.40  ----------------------
% 2.40/1.40  #Ref     : 4
% 2.40/1.40  #Sup     : 41
% 2.40/1.40  #Fact    : 0
% 2.40/1.40  #Define  : 0
% 2.40/1.40  #Split   : 3
% 2.40/1.40  #Chain   : 0
% 2.40/1.40  #Close   : 0
% 2.40/1.40  
% 2.40/1.40  Ordering : KBO
% 2.40/1.40  
% 2.40/1.40  Simplification rules
% 2.40/1.40  ----------------------
% 2.40/1.40  #Subsume      : 7
% 2.40/1.40  #Demod        : 32
% 2.40/1.40  #Tautology    : 20
% 2.40/1.40  #SimpNegUnit  : 12
% 2.40/1.40  #BackRed      : 4
% 2.40/1.40  
% 2.40/1.40  #Partial instantiations: 0
% 2.40/1.40  #Strategies tried      : 1
% 2.40/1.40  
% 2.40/1.40  Timing (in seconds)
% 2.40/1.40  ----------------------
% 2.40/1.40  Preprocessing        : 0.29
% 2.40/1.40  Parsing              : 0.15
% 2.40/1.40  CNF conversion       : 0.02
% 2.40/1.40  Main loop            : 0.28
% 2.40/1.40  Inferencing          : 0.10
% 2.40/1.40  Reduction            : 0.08
% 2.40/1.40  Demodulation         : 0.05
% 2.40/1.40  BG Simplification    : 0.01
% 2.40/1.40  Subsumption          : 0.05
% 2.40/1.40  Abstraction          : 0.01
% 2.40/1.40  MUC search           : 0.00
% 2.40/1.40  Cooper               : 0.00
% 2.40/1.40  Total                : 0.61
% 2.40/1.40  Index Insertion      : 0.00
% 2.40/1.40  Index Deletion       : 0.00
% 2.40/1.40  Index Matching       : 0.00
% 2.40/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
