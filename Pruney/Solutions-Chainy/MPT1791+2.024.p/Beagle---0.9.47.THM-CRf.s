%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:52 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 162 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 486 expanded)
%              Number of equality atoms :   26 (  80 expanded)
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

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_47,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_92,plain,(
    ! [B_32,A_33] :
      ( r2_hidden(B_32,k5_tmap_1(A_33,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_97,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_94])).

tff(c_98,plain,(
    r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_97])).

tff(c_149,plain,(
    ! [A_36,B_37] :
      ( u1_pre_topc(k6_tmap_1(A_36,B_37)) = k5_tmap_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_155,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_160,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_155])).

tff(c_161,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_160])).

tff(c_84,plain,(
    ! [A_30,B_31] :
      ( l1_pre_topc(k6_tmap_1(A_30,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_87,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_90,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_87])).

tff(c_91,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_90])).

tff(c_99,plain,(
    ! [A_34,B_35] :
      ( u1_struct_0(k6_tmap_1(A_34,B_35)) = u1_struct_0(A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_102,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_105,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_102])).

tff(c_106,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_105])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [B_3] :
      ( v3_pre_topc(B_3,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_3,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_141,plain,(
    ! [B_3] :
      ( v3_pre_topc(B_3,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_3,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_124])).

tff(c_174,plain,(
    ! [B_39] :
      ( v3_pre_topc(B_39,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_39,k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_141])).

tff(c_177,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_174])).

tff(c_180,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_177])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46])).

tff(c_305,plain,(
    ! [B_52,A_53] :
      ( v3_pre_topc(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(A_53)))))
      | ~ v3_pre_topc(B_52,g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_317,plain,(
    ! [B_52] :
      ( v3_pre_topc(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ v3_pre_topc(B_52,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_305])).

tff(c_325,plain,(
    ! [B_54] :
      ( v3_pre_topc(B_54,'#skF_1')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_54,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_48,c_106,c_317])).

tff(c_328,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_325])).

tff(c_331,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_328])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_331])).

tff(c_334,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_335,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_338,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,u1_pre_topc(A_56))
      | ~ v3_pre_topc(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_341,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_338])).

tff(c_344,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_335,c_341])).

tff(c_508,plain,(
    ! [A_81,B_82] :
      ( k5_tmap_1(A_81,B_82) = u1_pre_topc(A_81)
      | ~ r2_hidden(B_82,u1_pre_topc(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_514,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_508])).

tff(c_519,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_344,c_514])).

tff(c_520,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_519])).

tff(c_492,plain,(
    ! [A_79,B_80] :
      ( g1_pre_topc(u1_struct_0(A_79),k5_tmap_1(A_79,B_80)) = k6_tmap_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_496,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_492])).

tff(c_501,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_496])).

tff(c_502,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_501])).

tff(c_521,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_502])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.37  
% 2.72/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.37  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.72/1.37  
% 2.72/1.37  %Foreground sorts:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Background operators:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Foreground operators:
% 2.72/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.37  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.72/1.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.37  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.72/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.72/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.37  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.72/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.37  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.72/1.37  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.72/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.37  
% 2.72/1.39  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.72/1.39  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tmap_1)).
% 2.72/1.39  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.72/1.39  tff(f_74, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.72/1.39  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.72/1.39  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 2.72/1.39  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.72/1.39  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.72/1.39  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.39  tff(c_47, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 2.72/1.39  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.39  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.39  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.39  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.39  tff(c_92, plain, (![B_32, A_33]: (r2_hidden(B_32, k5_tmap_1(A_33, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.39  tff(c_94, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_92])).
% 2.72/1.39  tff(c_97, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_94])).
% 2.72/1.39  tff(c_98, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_97])).
% 2.72/1.39  tff(c_149, plain, (![A_36, B_37]: (u1_pre_topc(k6_tmap_1(A_36, B_37))=k5_tmap_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.72/1.39  tff(c_155, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_149])).
% 2.72/1.39  tff(c_160, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_155])).
% 2.72/1.39  tff(c_161, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_160])).
% 2.72/1.39  tff(c_84, plain, (![A_30, B_31]: (l1_pre_topc(k6_tmap_1(A_30, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.39  tff(c_87, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_84])).
% 2.72/1.39  tff(c_90, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_87])).
% 2.72/1.39  tff(c_91, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_90])).
% 2.72/1.39  tff(c_99, plain, (![A_34, B_35]: (u1_struct_0(k6_tmap_1(A_34, B_35))=u1_struct_0(A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.72/1.39  tff(c_102, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_99])).
% 2.72/1.39  tff(c_105, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_102])).
% 2.72/1.39  tff(c_106, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_105])).
% 2.72/1.39  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.39  tff(c_124, plain, (![B_3]: (v3_pre_topc(B_3, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_3, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 2.72/1.39  tff(c_141, plain, (![B_3]: (v3_pre_topc(B_3, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_3, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_124])).
% 2.72/1.39  tff(c_174, plain, (![B_39]: (v3_pre_topc(B_39, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_39, k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_141])).
% 2.72/1.39  tff(c_177, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_174])).
% 2.72/1.39  tff(c_180, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_177])).
% 2.72/1.39  tff(c_46, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.39  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47, c_46])).
% 2.72/1.39  tff(c_305, plain, (![B_52, A_53]: (v3_pre_topc(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(A_53))))) | ~v3_pre_topc(B_52, g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.39  tff(c_317, plain, (![B_52]: (v3_pre_topc(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~v3_pre_topc(B_52, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_305])).
% 2.72/1.39  tff(c_325, plain, (![B_54]: (v3_pre_topc(B_54, '#skF_1') | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_54, k6_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_48, c_106, c_317])).
% 2.72/1.39  tff(c_328, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_325])).
% 2.72/1.39  tff(c_331, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_328])).
% 2.72/1.39  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_331])).
% 2.72/1.39  tff(c_334, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.39  tff(c_335, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 2.72/1.39  tff(c_338, plain, (![B_55, A_56]: (r2_hidden(B_55, u1_pre_topc(A_56)) | ~v3_pre_topc(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.39  tff(c_341, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_338])).
% 2.72/1.39  tff(c_344, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_335, c_341])).
% 2.72/1.39  tff(c_508, plain, (![A_81, B_82]: (k5_tmap_1(A_81, B_82)=u1_pre_topc(A_81) | ~r2_hidden(B_82, u1_pre_topc(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.72/1.39  tff(c_514, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_508])).
% 2.72/1.39  tff(c_519, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_344, c_514])).
% 2.72/1.39  tff(c_520, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_519])).
% 2.72/1.39  tff(c_492, plain, (![A_79, B_80]: (g1_pre_topc(u1_struct_0(A_79), k5_tmap_1(A_79, B_80))=k6_tmap_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.39  tff(c_496, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_492])).
% 2.72/1.39  tff(c_501, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_496])).
% 2.72/1.39  tff(c_502, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_501])).
% 2.72/1.39  tff(c_521, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_502])).
% 2.72/1.39  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_521])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 87
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 3
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 6
% 2.72/1.39  #Demod        : 184
% 2.72/1.39  #Tautology    : 45
% 2.72/1.39  #SimpNegUnit  : 23
% 2.72/1.39  #BackRed      : 6
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.39  Preprocessing        : 0.31
% 2.72/1.39  Parsing              : 0.16
% 2.72/1.39  CNF conversion       : 0.02
% 2.72/1.39  Main loop            : 0.28
% 2.72/1.39  Inferencing          : 0.09
% 2.72/1.39  Reduction            : 0.10
% 2.72/1.39  Demodulation         : 0.07
% 2.72/1.39  BG Simplification    : 0.02
% 2.72/1.39  Subsumption          : 0.05
% 2.72/1.39  Abstraction          : 0.02
% 2.72/1.39  MUC search           : 0.00
% 2.72/1.39  Cooper               : 0.00
% 2.72/1.39  Total                : 0.63
% 2.72/1.39  Index Insertion      : 0.00
% 2.72/1.39  Index Deletion       : 0.00
% 2.72/1.39  Index Matching       : 0.00
% 2.72/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
