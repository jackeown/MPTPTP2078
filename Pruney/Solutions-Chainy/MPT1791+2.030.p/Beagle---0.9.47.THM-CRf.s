%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 164 expanded)
%              Number of leaves         :   25 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 486 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    ! [B_27,A_28] :
      ( v3_pre_topc(B_27,A_28)
      | ~ r2_hidden(B_27,u1_pre_topc(A_28))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_57,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_54])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_57])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_64])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_225,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,u1_pre_topc(A_45))
      | k5_tmap_1(A_45,B_44) != u1_pre_topc(A_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_234,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_225])).

tff(c_242,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_234])).

tff(c_243,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_65,c_242])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_245,plain,(
    ! [A_46,B_47] :
      ( k5_tmap_1(A_46,B_47) = u1_pre_topc(A_46)
      | ~ r2_hidden(B_47,u1_pre_topc(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,(
    ! [A_48] :
      ( k5_tmap_1(A_48,k1_xboole_0) = u1_pre_topc(A_48)
      | ~ r2_hidden(k1_xboole_0,u1_pre_topc(A_48))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_245])).

tff(c_281,plain,(
    ! [A_49] :
      ( k5_tmap_1(A_49,k1_xboole_0) = u1_pre_topc(A_49)
      | v2_struct_0(A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_10,c_265])).

tff(c_284,plain,
    ( k5_tmap_1('#skF_1',k1_xboole_0) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_281,c_28])).

tff(c_287,plain,(
    k5_tmap_1('#skF_1',k1_xboole_0) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_284])).

tff(c_136,plain,(
    ! [A_37,B_38] :
      ( u1_pre_topc(k6_tmap_1(A_37,B_38)) = k5_tmap_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_145,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_152,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_145])).

tff(c_153,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_152])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_49,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36])).

tff(c_187,plain,(
    ! [A_40,B_41] :
      ( g1_pre_topc(u1_struct_0(A_40),k5_tmap_1(A_40,B_41)) = k6_tmap_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_202,plain,(
    ! [A_40] :
      ( g1_pre_topc(u1_struct_0(A_40),k5_tmap_1(A_40,k1_xboole_0)) = k6_tmap_1(A_40,k1_xboole_0)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_2,c_187])).

tff(c_294,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1',k1_xboole_0)
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_202])).

tff(c_301,plain,
    ( k6_tmap_1('#skF_1',k1_xboole_0) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_49,c_294])).

tff(c_302,plain,(
    k6_tmap_1('#skF_1',k1_xboole_0) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_301])).

tff(c_154,plain,(
    ! [A_37] :
      ( u1_pre_topc(k6_tmap_1(A_37,k1_xboole_0)) = k5_tmap_1(A_37,k1_xboole_0)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_2,c_136])).

tff(c_307,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1',k1_xboole_0)
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_154])).

tff(c_314,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_287,c_153,c_307])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_243,c_314])).

tff(c_317,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_318,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_333,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,u1_pre_topc(A_53))
      | ~ v3_pre_topc(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_336,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_333])).

tff(c_343,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_318,c_336])).

tff(c_509,plain,(
    ! [A_69,B_70] :
      ( k5_tmap_1(A_69,B_70) = u1_pre_topc(A_69)
      | ~ r2_hidden(B_70,u1_pre_topc(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_518,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_509])).

tff(c_526,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_343,c_518])).

tff(c_527,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_526])).

tff(c_433,plain,(
    ! [A_62,B_63] :
      ( g1_pre_topc(u1_struct_0(A_62),k5_tmap_1(A_62,B_63)) = k6_tmap_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_439,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_433])).

tff(c_446,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_439])).

tff(c_447,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_446])).

tff(c_529,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_447])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:55:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.67/1.41  
% 2.67/1.41  %Foreground sorts:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Background operators:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Foreground operators:
% 2.67/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.41  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.67/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.41  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.67/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.41  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.41  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.67/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.41  
% 2.67/1.42  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.67/1.42  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.67/1.42  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.67/1.42  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 2.67/1.42  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.42  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.67/1.42  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.67/1.42  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.42  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.42  tff(c_48, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 2.67/1.42  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.42  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.42  tff(c_54, plain, (![B_27, A_28]: (v3_pre_topc(B_27, A_28) | ~r2_hidden(B_27, u1_pre_topc(A_28)) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.42  tff(c_57, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_54])).
% 2.67/1.42  tff(c_64, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_57])).
% 2.67/1.42  tff(c_65, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_64])).
% 2.67/1.42  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.42  tff(c_225, plain, (![B_44, A_45]: (r2_hidden(B_44, u1_pre_topc(A_45)) | k5_tmap_1(A_45, B_44)!=u1_pre_topc(A_45) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.42  tff(c_234, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_225])).
% 2.67/1.42  tff(c_242, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_234])).
% 2.67/1.42  tff(c_243, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_28, c_65, c_242])).
% 2.67/1.42  tff(c_10, plain, (![A_8]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.42  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.42  tff(c_245, plain, (![A_46, B_47]: (k5_tmap_1(A_46, B_47)=u1_pre_topc(A_46) | ~r2_hidden(B_47, u1_pre_topc(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.42  tff(c_265, plain, (![A_48]: (k5_tmap_1(A_48, k1_xboole_0)=u1_pre_topc(A_48) | ~r2_hidden(k1_xboole_0, u1_pre_topc(A_48)) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_2, c_245])).
% 2.67/1.42  tff(c_281, plain, (![A_49]: (k5_tmap_1(A_49, k1_xboole_0)=u1_pre_topc(A_49) | v2_struct_0(A_49) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(resolution, [status(thm)], [c_10, c_265])).
% 2.67/1.42  tff(c_284, plain, (k5_tmap_1('#skF_1', k1_xboole_0)=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_281, c_28])).
% 2.67/1.42  tff(c_287, plain, (k5_tmap_1('#skF_1', k1_xboole_0)=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_284])).
% 2.67/1.42  tff(c_136, plain, (![A_37, B_38]: (u1_pre_topc(k6_tmap_1(A_37, B_38))=k5_tmap_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.67/1.42  tff(c_145, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_136])).
% 2.67/1.42  tff(c_152, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_145])).
% 2.67/1.42  tff(c_153, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_152])).
% 2.67/1.42  tff(c_36, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.67/1.42  tff(c_49, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_36])).
% 2.67/1.42  tff(c_187, plain, (![A_40, B_41]: (g1_pre_topc(u1_struct_0(A_40), k5_tmap_1(A_40, B_41))=k6_tmap_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.42  tff(c_202, plain, (![A_40]: (g1_pre_topc(u1_struct_0(A_40), k5_tmap_1(A_40, k1_xboole_0))=k6_tmap_1(A_40, k1_xboole_0) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(resolution, [status(thm)], [c_2, c_187])).
% 2.67/1.42  tff(c_294, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', k1_xboole_0) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_287, c_202])).
% 2.67/1.42  tff(c_301, plain, (k6_tmap_1('#skF_1', k1_xboole_0)=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_49, c_294])).
% 2.67/1.42  tff(c_302, plain, (k6_tmap_1('#skF_1', k1_xboole_0)=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_301])).
% 2.67/1.42  tff(c_154, plain, (![A_37]: (u1_pre_topc(k6_tmap_1(A_37, k1_xboole_0))=k5_tmap_1(A_37, k1_xboole_0) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(resolution, [status(thm)], [c_2, c_136])).
% 2.67/1.42  tff(c_307, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', k1_xboole_0) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_302, c_154])).
% 2.67/1.42  tff(c_314, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_287, c_153, c_307])).
% 2.67/1.42  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_243, c_314])).
% 2.67/1.42  tff(c_317, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.67/1.42  tff(c_318, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.67/1.42  tff(c_333, plain, (![B_52, A_53]: (r2_hidden(B_52, u1_pre_topc(A_53)) | ~v3_pre_topc(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.42  tff(c_336, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_333])).
% 2.67/1.42  tff(c_343, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_318, c_336])).
% 2.67/1.42  tff(c_509, plain, (![A_69, B_70]: (k5_tmap_1(A_69, B_70)=u1_pre_topc(A_69) | ~r2_hidden(B_70, u1_pre_topc(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.42  tff(c_518, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_509])).
% 2.67/1.42  tff(c_526, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_343, c_518])).
% 2.67/1.42  tff(c_527, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_28, c_526])).
% 2.67/1.42  tff(c_433, plain, (![A_62, B_63]: (g1_pre_topc(u1_struct_0(A_62), k5_tmap_1(A_62, B_63))=k6_tmap_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.42  tff(c_439, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_433])).
% 2.67/1.42  tff(c_446, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_439])).
% 2.67/1.42  tff(c_447, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_446])).
% 2.67/1.42  tff(c_529, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_447])).
% 2.67/1.42  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_529])).
% 2.67/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  Inference rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Ref     : 0
% 2.67/1.42  #Sup     : 117
% 2.67/1.42  #Fact    : 0
% 2.67/1.42  #Define  : 0
% 2.67/1.42  #Split   : 6
% 2.67/1.42  #Chain   : 0
% 2.67/1.42  #Close   : 0
% 2.67/1.42  
% 2.67/1.42  Ordering : KBO
% 2.67/1.42  
% 2.67/1.42  Simplification rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Subsume      : 14
% 2.67/1.42  #Demod        : 55
% 2.67/1.42  #Tautology    : 36
% 2.67/1.42  #SimpNegUnit  : 18
% 2.67/1.42  #BackRed      : 2
% 2.67/1.42  
% 2.67/1.42  #Partial instantiations: 0
% 2.67/1.42  #Strategies tried      : 1
% 2.67/1.42  
% 2.67/1.42  Timing (in seconds)
% 2.67/1.42  ----------------------
% 2.67/1.42  Preprocessing        : 0.32
% 2.67/1.42  Parsing              : 0.18
% 2.67/1.42  CNF conversion       : 0.02
% 2.67/1.42  Main loop            : 0.30
% 2.67/1.42  Inferencing          : 0.12
% 2.67/1.42  Reduction            : 0.09
% 2.67/1.42  Demodulation         : 0.06
% 2.67/1.42  BG Simplification    : 0.02
% 2.67/1.43  Subsumption          : 0.05
% 2.67/1.43  Abstraction          : 0.02
% 2.67/1.43  MUC search           : 0.00
% 2.67/1.43  Cooper               : 0.00
% 2.67/1.43  Total                : 0.65
% 2.67/1.43  Index Insertion      : 0.00
% 2.67/1.43  Index Deletion       : 0.00
% 2.67/1.43  Index Matching       : 0.00
% 2.67/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
