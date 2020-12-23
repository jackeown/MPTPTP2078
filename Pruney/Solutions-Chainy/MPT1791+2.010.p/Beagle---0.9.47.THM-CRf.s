%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:50 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 205 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  216 ( 637 expanded)
%              Number of equality atoms :   33 ( 103 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_113,plain,(
    ! [B_31,A_32] :
      ( r2_hidden(B_31,k5_tmap_1(A_32,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_115,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_118,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_115])).

tff(c_119,plain,(
    r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_118])).

tff(c_171,plain,(
    ! [A_35,B_36] :
      ( u1_pre_topc(k6_tmap_1(A_35,B_36)) = k5_tmap_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_177,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_182,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_177])).

tff(c_183,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_182])).

tff(c_105,plain,(
    ! [A_29,B_30] :
      ( l1_pre_topc(k6_tmap_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_111,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_108])).

tff(c_112,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_111])).

tff(c_120,plain,(
    ! [A_33,B_34] :
      ( u1_struct_0(k6_tmap_1(A_33,B_34)) = u1_struct_0(A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_123,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_126,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_123])).

tff(c_127,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_126])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v3_pre_topc(B_4,A_2)
      | ~ r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_4,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_4])).

tff(c_165,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_4,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_145])).

tff(c_203,plain,(
    ! [B_37] :
      ( v3_pre_topc(B_37,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_37,k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_165])).

tff(c_206,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_203])).

tff(c_209,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_206])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_57,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46])).

tff(c_329,plain,(
    ! [B_48,A_49] :
      ( v3_pre_topc(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_49),u1_pre_topc(A_49)))))
      | ~ v3_pre_topc(B_48,g1_pre_topc(u1_struct_0(A_49),u1_pre_topc(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_341,plain,(
    ! [B_48] :
      ( v3_pre_topc(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ v3_pre_topc(B_48,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_329])).

tff(c_352,plain,(
    ! [B_50] :
      ( v3_pre_topc(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_50,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_57,c_127,c_341])).

tff(c_355,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_352])).

tff(c_358,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_355])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_358])).

tff(c_361,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_362,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_371,plain,(
    ! [B_51,A_52] :
      ( r2_hidden(B_51,u1_pre_topc(A_52))
      | ~ v3_pre_topc(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_374,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_371])).

tff(c_377,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_362,c_374])).

tff(c_543,plain,(
    ! [A_73,B_74] :
      ( k5_tmap_1(A_73,B_74) = u1_pre_topc(A_73)
      | ~ r2_hidden(B_74,u1_pre_topc(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_549,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_543])).

tff(c_554,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_377,c_549])).

tff(c_555,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_554])).

tff(c_393,plain,(
    ! [A_57,B_58] :
      ( l1_pre_topc(k6_tmap_1(A_57,B_58))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_396,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_393])).

tff(c_399,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_396])).

tff(c_400,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_399])).

tff(c_385,plain,(
    ! [A_55,B_56] :
      ( v1_pre_topc(k6_tmap_1(A_55,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_388,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_385])).

tff(c_391,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_388])).

tff(c_392,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_391])).

tff(c_416,plain,(
    ! [A_63,B_64] :
      ( u1_struct_0(k6_tmap_1(A_63,B_64)) = u1_struct_0(A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_419,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_416])).

tff(c_422,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_419])).

tff(c_423,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_422])).

tff(c_467,plain,(
    ! [A_65,B_66] :
      ( u1_pre_topc(k6_tmap_1(A_65,B_66)) = k5_tmap_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_473,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_467])).

tff(c_478,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_473])).

tff(c_479,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_478])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_483,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_2])).

tff(c_487,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_392,c_423,c_483])).

tff(c_558,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_487])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.72/1.40  
% 2.72/1.40  %Foreground sorts:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Background operators:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Foreground operators:
% 2.72/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.72/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.40  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.72/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.72/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.72/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.40  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.72/1.40  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.72/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.40  
% 2.72/1.42  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.72/1.42  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tmap_1)).
% 2.72/1.42  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.72/1.42  tff(f_68, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.72/1.42  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.72/1.42  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 2.72/1.42  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.72/1.42  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.72/1.42  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.72/1.42  tff(c_56, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 2.72/1.42  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.72/1.42  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.72/1.42  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.72/1.42  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.72/1.42  tff(c_113, plain, (![B_31, A_32]: (r2_hidden(B_31, k5_tmap_1(A_32, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.72/1.42  tff(c_115, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.72/1.42  tff(c_118, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_115])).
% 2.72/1.42  tff(c_119, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_118])).
% 2.72/1.42  tff(c_171, plain, (![A_35, B_36]: (u1_pre_topc(k6_tmap_1(A_35, B_36))=k5_tmap_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.42  tff(c_177, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_171])).
% 2.72/1.42  tff(c_182, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_177])).
% 2.72/1.42  tff(c_183, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_182])).
% 2.72/1.42  tff(c_105, plain, (![A_29, B_30]: (l1_pre_topc(k6_tmap_1(A_29, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.42  tff(c_108, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_105])).
% 2.72/1.42  tff(c_111, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_108])).
% 2.72/1.42  tff(c_112, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_111])).
% 2.72/1.42  tff(c_120, plain, (![A_33, B_34]: (u1_struct_0(k6_tmap_1(A_33, B_34))=u1_struct_0(A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.42  tff(c_123, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_120])).
% 2.72/1.42  tff(c_126, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_123])).
% 2.72/1.42  tff(c_127, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_126])).
% 2.72/1.42  tff(c_4, plain, (![B_4, A_2]: (v3_pre_topc(B_4, A_2) | ~r2_hidden(B_4, u1_pre_topc(A_2)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.72/1.42  tff(c_145, plain, (![B_4]: (v3_pre_topc(B_4, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_4, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_4])).
% 2.72/1.42  tff(c_165, plain, (![B_4]: (v3_pre_topc(B_4, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_4, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_145])).
% 2.72/1.42  tff(c_203, plain, (![B_37]: (v3_pre_topc(B_37, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_37, k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_165])).
% 2.72/1.42  tff(c_206, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_203])).
% 2.72/1.42  tff(c_209, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_206])).
% 2.72/1.42  tff(c_46, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.72/1.42  tff(c_57, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_46])).
% 2.72/1.42  tff(c_329, plain, (![B_48, A_49]: (v3_pre_topc(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_49), u1_pre_topc(A_49))))) | ~v3_pre_topc(B_48, g1_pre_topc(u1_struct_0(A_49), u1_pre_topc(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.42  tff(c_341, plain, (![B_48]: (v3_pre_topc(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~v3_pre_topc(B_48, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_329])).
% 2.72/1.42  tff(c_352, plain, (![B_50]: (v3_pre_topc(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_50, k6_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_57, c_127, c_341])).
% 2.72/1.42  tff(c_355, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_352])).
% 2.72/1.42  tff(c_358, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_355])).
% 2.72/1.42  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_358])).
% 2.72/1.42  tff(c_361, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.42  tff(c_362, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.42  tff(c_371, plain, (![B_51, A_52]: (r2_hidden(B_51, u1_pre_topc(A_52)) | ~v3_pre_topc(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.72/1.42  tff(c_374, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_371])).
% 2.72/1.42  tff(c_377, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_362, c_374])).
% 2.72/1.42  tff(c_543, plain, (![A_73, B_74]: (k5_tmap_1(A_73, B_74)=u1_pre_topc(A_73) | ~r2_hidden(B_74, u1_pre_topc(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.72/1.42  tff(c_549, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_543])).
% 2.72/1.42  tff(c_554, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_377, c_549])).
% 2.72/1.42  tff(c_555, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_554])).
% 2.72/1.42  tff(c_393, plain, (![A_57, B_58]: (l1_pre_topc(k6_tmap_1(A_57, B_58)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.42  tff(c_396, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_393])).
% 2.72/1.42  tff(c_399, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_396])).
% 2.72/1.42  tff(c_400, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_399])).
% 2.72/1.42  tff(c_385, plain, (![A_55, B_56]: (v1_pre_topc(k6_tmap_1(A_55, B_56)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.42  tff(c_388, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_385])).
% 2.72/1.42  tff(c_391, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_388])).
% 2.72/1.42  tff(c_392, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_391])).
% 2.72/1.42  tff(c_416, plain, (![A_63, B_64]: (u1_struct_0(k6_tmap_1(A_63, B_64))=u1_struct_0(A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.42  tff(c_419, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_416])).
% 2.72/1.42  tff(c_422, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_419])).
% 2.72/1.42  tff(c_423, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_422])).
% 2.72/1.42  tff(c_467, plain, (![A_65, B_66]: (u1_pre_topc(k6_tmap_1(A_65, B_66))=k5_tmap_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.42  tff(c_473, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_467])).
% 2.72/1.42  tff(c_478, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_473])).
% 2.72/1.42  tff(c_479, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_478])).
% 2.72/1.42  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.42  tff(c_483, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_479, c_2])).
% 2.72/1.42  tff(c_487, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_392, c_423, c_483])).
% 2.72/1.42  tff(c_558, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_487])).
% 2.72/1.42  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_558])).
% 2.72/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.42  
% 2.72/1.42  Inference rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Ref     : 0
% 2.72/1.42  #Sup     : 95
% 2.72/1.42  #Fact    : 0
% 2.72/1.42  #Define  : 0
% 2.72/1.42  #Split   : 6
% 2.72/1.42  #Chain   : 0
% 2.72/1.42  #Close   : 0
% 2.72/1.42  
% 2.72/1.42  Ordering : KBO
% 2.72/1.42  
% 2.72/1.42  Simplification rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Subsume      : 5
% 2.72/1.42  #Demod        : 193
% 2.72/1.42  #Tautology    : 52
% 2.72/1.42  #SimpNegUnit  : 21
% 2.72/1.42  #BackRed      : 5
% 2.72/1.42  
% 2.72/1.42  #Partial instantiations: 0
% 2.72/1.42  #Strategies tried      : 1
% 2.72/1.42  
% 2.72/1.42  Timing (in seconds)
% 2.72/1.42  ----------------------
% 2.72/1.42  Preprocessing        : 0.32
% 2.72/1.42  Parsing              : 0.16
% 2.72/1.42  CNF conversion       : 0.02
% 2.72/1.42  Main loop            : 0.29
% 2.72/1.42  Inferencing          : 0.10
% 2.72/1.42  Reduction            : 0.10
% 2.72/1.42  Demodulation         : 0.07
% 2.72/1.42  BG Simplification    : 0.02
% 2.72/1.42  Subsumption          : 0.05
% 2.72/1.42  Abstraction          : 0.02
% 2.72/1.42  MUC search           : 0.00
% 2.72/1.42  Cooper               : 0.00
% 2.72/1.42  Total                : 0.65
% 2.72/1.42  Index Insertion      : 0.00
% 2.72/1.42  Index Deletion       : 0.00
% 2.72/1.42  Index Matching       : 0.00
% 2.72/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
