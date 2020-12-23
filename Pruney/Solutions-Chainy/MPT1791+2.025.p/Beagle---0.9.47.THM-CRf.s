%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:52 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 409 expanded)
%              Number of leaves         :   30 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          :  223 (1250 expanded)
%              Number of equality atoms :   15 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
             => ( C = B
               => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_57,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_67,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_44])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_243,plain,(
    ! [A_62,B_63] :
      ( m1_pre_topc(A_62,g1_pre_topc(u1_struct_0(B_63),u1_pre_topc(B_63)))
      | ~ m1_pre_topc(A_62,B_63)
      | ~ l1_pre_topc(B_63)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_256,plain,(
    ! [A_62] :
      ( m1_pre_topc(A_62,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc(A_62,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_243])).

tff(c_262,plain,(
    ! [A_62] :
      ( m1_pre_topc(A_62,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc(A_62,'#skF_1')
      | ~ l1_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_256])).

tff(c_74,plain,(
    ! [B_44,A_45] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)),A_45)
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_85,plain,(
    ! [A_46] :
      ( m1_pre_topc(k6_tmap_1('#skF_1','#skF_2'),A_46)
      | ~ m1_pre_topc('#skF_1',A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_74])).

tff(c_6,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_46] :
      ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc('#skF_1',A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_102,plain,(
    ! [A_49] :
      ( ~ m1_pre_topc('#skF_1',A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_106])).

tff(c_111,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_285,plain,(
    ! [C_65,A_66,B_67] :
      ( m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(B_67)))
      | ~ m1_pre_topc(B_67,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_289,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_pre_topc('#skF_1',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_36,c_285])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ v3_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_300,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_2',u1_pre_topc(A_68))
      | ~ v3_pre_topc('#skF_2',A_68)
      | ~ m1_pre_topc('#skF_1',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_289,c_4])).

tff(c_8,plain,(
    ! [C_13,A_7,B_11] :
      ( m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(B_11)))
      | ~ m1_pre_topc(B_11,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_357,plain,(
    ! [A_72,A_73] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_pre_topc(A_73,A_72)
      | ~ l1_pre_topc(A_72)
      | ~ m1_pre_topc('#skF_1',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_289,c_8])).

tff(c_363,plain,(
    ! [A_62] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc('#skF_1',A_62)
      | ~ m1_pre_topc(A_62,'#skF_1')
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_262,c_357])).

tff(c_380,plain,(
    ! [A_62] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ m1_pre_topc('#skF_1',A_62)
      | ~ m1_pre_topc(A_62,'#skF_1')
      | ~ l1_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_363])).

tff(c_409,plain,(
    ! [A_77] :
      ( ~ m1_pre_topc('#skF_1',A_77)
      | ~ m1_pre_topc(A_77,'#skF_1')
      | ~ l1_pre_topc(A_77) ) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_418,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_409])).

tff(c_427,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_418])).

tff(c_443,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_427])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_443])).

tff(c_448,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_453,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_448,c_2])).

tff(c_460,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_453])).

tff(c_464,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_467,plain,
    ( ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_300,c_464])).

tff(c_470,plain,
    ( ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_467])).

tff(c_471,plain,(
    ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_489,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_262,c_471])).

tff(c_492,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_489])).

tff(c_495,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_492])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_495])).

tff(c_500,plain,(
    ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1130,plain,(
    ! [C_114,A_115] :
      ( v3_pre_topc(C_114,k6_tmap_1(A_115,C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_115,C_114))))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1141,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_448,c_1130])).

tff(c_1153,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1141])).

tff(c_1155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_500,c_1153])).

tff(c_1156,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_1791,plain,(
    ! [B_152,A_153] :
      ( v3_pre_topc(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)))))
      | ~ v3_pre_topc(B_152,g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1805,plain,(
    ! [B_152] :
      ( v3_pre_topc(B_152,'#skF_1')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ v3_pre_topc(B_152,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1791])).

tff(c_1811,plain,(
    ! [B_154] :
      ( v3_pre_topc(B_154,'#skF_1')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ v3_pre_topc(B_154,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_57,c_1805])).

tff(c_1821,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_448,c_1811])).

tff(c_1833,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_1821])).

tff(c_1835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1833])).

tff(c_1837,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1836,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1861,plain,(
    ! [B_163,A_164] :
      ( r2_hidden(B_163,u1_pre_topc(A_164))
      | ~ v3_pre_topc(B_163,A_164)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1864,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1861])).

tff(c_1867,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1836,c_1864])).

tff(c_1995,plain,(
    ! [A_189,B_190] :
      ( k5_tmap_1(A_189,B_190) = u1_pre_topc(A_189)
      | ~ r2_hidden(B_190,u1_pre_topc(A_189))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2001,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1995])).

tff(c_2005,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1867,c_2001])).

tff(c_2006,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2005])).

tff(c_2069,plain,(
    ! [A_199,B_200] :
      ( g1_pre_topc(u1_struct_0(A_199),k5_tmap_1(A_199,B_200)) = k6_tmap_1(A_199,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2073,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2069])).

tff(c_2077,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2006,c_2073])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1837,c_2077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.70  
% 4.09/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.70  %$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.09/1.70  
% 4.09/1.70  %Foreground sorts:
% 4.09/1.70  
% 4.09/1.70  
% 4.09/1.70  %Background operators:
% 4.09/1.70  
% 4.09/1.70  
% 4.09/1.70  %Foreground operators:
% 4.09/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.09/1.70  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.09/1.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.09/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.70  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.09/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.09/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.70  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.09/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.70  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 4.09/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.09/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.09/1.70  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 4.09/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.09/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.70  
% 4.09/1.72  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 4.09/1.72  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.09/1.72  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.09/1.72  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 4.09/1.72  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.09/1.72  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.09/1.72  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.09/1.72  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tmap_1)).
% 4.09/1.72  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 4.09/1.72  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 4.09/1.72  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 4.09/1.72  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.09/1.72  tff(c_50, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.09/1.72  tff(c_57, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 4.09/1.72  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.09/1.72  tff(c_67, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_44])).
% 4.09/1.72  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.09/1.72  tff(c_34, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.09/1.72  tff(c_243, plain, (![A_62, B_63]: (m1_pre_topc(A_62, g1_pre_topc(u1_struct_0(B_63), u1_pre_topc(B_63))) | ~m1_pre_topc(A_62, B_63) | ~l1_pre_topc(B_63) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.09/1.72  tff(c_256, plain, (![A_62]: (m1_pre_topc(A_62, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc(A_62, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_62))), inference(superposition, [status(thm), theory('equality')], [c_57, c_243])).
% 4.09/1.72  tff(c_262, plain, (![A_62]: (m1_pre_topc(A_62, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc(A_62, '#skF_1') | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_256])).
% 4.09/1.72  tff(c_74, plain, (![B_44, A_45]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44)), A_45) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.09/1.72  tff(c_85, plain, (![A_46]: (m1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'), A_46) | ~m1_pre_topc('#skF_1', A_46) | ~l1_pre_topc(A_46))), inference(superposition, [status(thm), theory('equality')], [c_57, c_74])).
% 4.09/1.72  tff(c_6, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.09/1.72  tff(c_92, plain, (![A_46]: (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_85, c_6])).
% 4.09/1.72  tff(c_102, plain, (![A_49]: (~m1_pre_topc('#skF_1', A_49) | ~l1_pre_topc(A_49))), inference(splitLeft, [status(thm)], [c_92])).
% 4.09/1.72  tff(c_106, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_102])).
% 4.09/1.72  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_106])).
% 4.09/1.72  tff(c_111, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_92])).
% 4.09/1.72  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.09/1.72  tff(c_285, plain, (![C_65, A_66, B_67]: (m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(B_67))) | ~m1_pre_topc(B_67, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.72  tff(c_289, plain, (![A_68]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_pre_topc('#skF_1', A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_36, c_285])).
% 4.09/1.72  tff(c_4, plain, (![B_3, A_1]: (r2_hidden(B_3, u1_pre_topc(A_1)) | ~v3_pre_topc(B_3, A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.09/1.72  tff(c_300, plain, (![A_68]: (r2_hidden('#skF_2', u1_pre_topc(A_68)) | ~v3_pre_topc('#skF_2', A_68) | ~m1_pre_topc('#skF_1', A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_289, c_4])).
% 4.09/1.72  tff(c_8, plain, (![C_13, A_7, B_11]: (m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(B_11))) | ~m1_pre_topc(B_11, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.72  tff(c_357, plain, (![A_72, A_73]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_pre_topc(A_73, A_72) | ~l1_pre_topc(A_72) | ~m1_pre_topc('#skF_1', A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_289, c_8])).
% 4.09/1.72  tff(c_363, plain, (![A_62]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', A_62) | ~m1_pre_topc(A_62, '#skF_1') | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_262, c_357])).
% 4.09/1.72  tff(c_380, plain, (![A_62]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~m1_pre_topc('#skF_1', A_62) | ~m1_pre_topc(A_62, '#skF_1') | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_363])).
% 4.09/1.72  tff(c_409, plain, (![A_77]: (~m1_pre_topc('#skF_1', A_77) | ~m1_pre_topc(A_77, '#skF_1') | ~l1_pre_topc(A_77))), inference(splitLeft, [status(thm)], [c_380])).
% 4.09/1.72  tff(c_418, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_409])).
% 4.09/1.72  tff(c_427, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_418])).
% 4.09/1.72  tff(c_443, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_427])).
% 4.09/1.72  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_443])).
% 4.09/1.72  tff(c_448, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_380])).
% 4.09/1.72  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.09/1.72  tff(c_453, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_448, c_2])).
% 4.09/1.72  tff(c_460, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_453])).
% 4.09/1.72  tff(c_464, plain, (~r2_hidden('#skF_2', u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_460])).
% 4.09/1.72  tff(c_467, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_300, c_464])).
% 4.09/1.72  tff(c_470, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_467])).
% 4.09/1.72  tff(c_471, plain, (~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_470])).
% 4.09/1.72  tff(c_489, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_262, c_471])).
% 4.09/1.72  tff(c_492, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_489])).
% 4.09/1.72  tff(c_495, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_492])).
% 4.09/1.72  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_495])).
% 4.09/1.72  tff(c_500, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_470])).
% 4.09/1.72  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.09/1.72  tff(c_1130, plain, (![C_114, A_115]: (v3_pre_topc(C_114, k6_tmap_1(A_115, C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_115, C_114)))) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.09/1.72  tff(c_1141, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_448, c_1130])).
% 4.09/1.72  tff(c_1153, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1141])).
% 4.09/1.72  tff(c_1155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_500, c_1153])).
% 4.09/1.72  tff(c_1156, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_460])).
% 4.09/1.72  tff(c_1791, plain, (![B_152, A_153]: (v3_pre_topc(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153))))) | ~v3_pre_topc(B_152, g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.09/1.72  tff(c_1805, plain, (![B_152]: (v3_pre_topc(B_152, '#skF_1') | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~v3_pre_topc(B_152, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_1791])).
% 4.09/1.72  tff(c_1811, plain, (![B_154]: (v3_pre_topc(B_154, '#skF_1') | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~v3_pre_topc(B_154, k6_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_57, c_1805])).
% 4.09/1.72  tff(c_1821, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_448, c_1811])).
% 4.09/1.72  tff(c_1833, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_1821])).
% 4.09/1.72  tff(c_1835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_1833])).
% 4.09/1.72  tff(c_1837, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.09/1.72  tff(c_1836, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.09/1.72  tff(c_1861, plain, (![B_163, A_164]: (r2_hidden(B_163, u1_pre_topc(A_164)) | ~v3_pre_topc(B_163, A_164) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.09/1.72  tff(c_1864, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1861])).
% 4.09/1.72  tff(c_1867, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1836, c_1864])).
% 4.09/1.72  tff(c_1995, plain, (![A_189, B_190]: (k5_tmap_1(A_189, B_190)=u1_pre_topc(A_189) | ~r2_hidden(B_190, u1_pre_topc(A_189)) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.09/1.72  tff(c_2001, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1995])).
% 4.09/1.72  tff(c_2005, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1867, c_2001])).
% 4.09/1.72  tff(c_2006, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_2005])).
% 4.09/1.72  tff(c_2069, plain, (![A_199, B_200]: (g1_pre_topc(u1_struct_0(A_199), k5_tmap_1(A_199, B_200))=k6_tmap_1(A_199, B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.09/1.72  tff(c_2073, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2069])).
% 4.09/1.72  tff(c_2077, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2006, c_2073])).
% 4.09/1.72  tff(c_2079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1837, c_2077])).
% 4.09/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.72  
% 4.09/1.72  Inference rules
% 4.09/1.72  ----------------------
% 4.09/1.72  #Ref     : 0
% 4.09/1.72  #Sup     : 394
% 4.09/1.72  #Fact    : 0
% 4.09/1.72  #Define  : 0
% 4.09/1.72  #Split   : 9
% 4.09/1.72  #Chain   : 0
% 4.09/1.72  #Close   : 0
% 4.09/1.72  
% 4.09/1.72  Ordering : KBO
% 4.09/1.72  
% 4.09/1.72  Simplification rules
% 4.09/1.72  ----------------------
% 4.09/1.72  #Subsume      : 116
% 4.09/1.72  #Demod        : 399
% 4.09/1.72  #Tautology    : 110
% 4.09/1.72  #SimpNegUnit  : 40
% 4.09/1.72  #BackRed      : 0
% 4.09/1.72  
% 4.09/1.72  #Partial instantiations: 0
% 4.09/1.72  #Strategies tried      : 1
% 4.09/1.72  
% 4.09/1.72  Timing (in seconds)
% 4.09/1.72  ----------------------
% 4.09/1.73  Preprocessing        : 0.35
% 4.09/1.73  Parsing              : 0.18
% 4.09/1.73  CNF conversion       : 0.02
% 4.09/1.73  Main loop            : 0.61
% 4.09/1.73  Inferencing          : 0.22
% 4.09/1.73  Reduction            : 0.19
% 4.09/1.73  Demodulation         : 0.13
% 4.09/1.73  BG Simplification    : 0.03
% 4.09/1.73  Subsumption          : 0.13
% 4.09/1.73  Abstraction          : 0.03
% 4.09/1.73  MUC search           : 0.00
% 4.09/1.73  Cooper               : 0.00
% 4.09/1.73  Total                : 1.00
% 4.09/1.73  Index Insertion      : 0.00
% 4.09/1.73  Index Deletion       : 0.00
% 4.09/1.73  Index Matching       : 0.00
% 4.09/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
