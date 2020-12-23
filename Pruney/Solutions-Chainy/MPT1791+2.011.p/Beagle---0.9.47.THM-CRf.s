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
% DateTime   : Thu Dec  3 10:27:50 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 316 expanded)
%              Number of leaves         :   26 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  239 (1029 expanded)
%              Number of equality atoms :   34 ( 165 expanded)
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

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_165,plain,(
    ! [A_37,B_38] :
      ( u1_pre_topc(k6_tmap_1(A_37,B_38)) = k5_tmap_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_171,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_165])).

tff(c_176,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_171])).

tff(c_177,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_176])).

tff(c_105,plain,(
    ! [A_33,B_34] :
      ( l1_pre_topc(k6_tmap_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
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

tff(c_113,plain,(
    ! [A_35,B_36] :
      ( u1_struct_0(k6_tmap_1(A_35,B_36)) = u1_struct_0(A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_116,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_119,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_116])).

tff(c_120,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_119])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v3_pre_topc(B_4,A_2)
      | ~ r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_136,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_4,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_4])).

tff(c_154,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_4,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_136])).

tff(c_196,plain,(
    ! [B_39] :
      ( v3_pre_topc(B_39,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r2_hidden(B_39,k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_154])).

tff(c_200,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_196])).

tff(c_201,plain,(
    ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ v3_pre_topc(B_4,A_2)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_139,plain,(
    ! [B_4] :
      ( r2_hidden(B_4,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ v3_pre_topc(B_4,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_6])).

tff(c_156,plain,(
    ! [B_4] :
      ( r2_hidden(B_4,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ v3_pre_topc(B_4,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_139])).

tff(c_227,plain,(
    ! [B_43] :
      ( r2_hidden(B_43,k5_tmap_1('#skF_1','#skF_2'))
      | ~ v3_pre_topc(B_43,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_156])).

tff(c_230,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_227])).

tff(c_233,plain,(
    ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_230])).

tff(c_317,plain,(
    ! [C_50,A_51] :
      ( v3_pre_topc(C_50,k6_tmap_1(A_51,C_50))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_51,C_50))))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_320,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_317])).

tff(c_322,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_32,c_320])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_233,c_322])).

tff(c_325,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_57,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46])).

tff(c_450,plain,(
    ! [B_64,A_65] :
      ( v3_pre_topc(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_65),u1_pre_topc(A_65)))))
      | ~ v3_pre_topc(B_64,g1_pre_topc(u1_struct_0(A_65),u1_pre_topc(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_462,plain,(
    ! [B_64] :
      ( v3_pre_topc(B_64,'#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ v3_pre_topc(B_64,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_450])).

tff(c_473,plain,(
    ! [B_66] :
      ( v3_pre_topc(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_66,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_57,c_120,c_462])).

tff(c_476,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_473])).

tff(c_479,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_476])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_479])).

tff(c_482,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_483,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_499,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,u1_pre_topc(A_70))
      | ~ v3_pre_topc(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_502,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_499])).

tff(c_505,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_483,c_502])).

tff(c_682,plain,(
    ! [A_90,B_91] :
      ( k5_tmap_1(A_90,B_91) = u1_pre_topc(A_90)
      | ~ r2_hidden(B_91,u1_pre_topc(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_688,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_682])).

tff(c_693,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_505,c_688])).

tff(c_694,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_693])).

tff(c_514,plain,(
    ! [A_73,B_74] :
      ( l1_pre_topc(k6_tmap_1(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_517,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_514])).

tff(c_520,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_517])).

tff(c_521,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_520])).

tff(c_522,plain,(
    ! [A_75,B_76] :
      ( v1_pre_topc(k6_tmap_1(A_75,B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_525,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_522])).

tff(c_528,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_525])).

tff(c_529,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_528])).

tff(c_530,plain,(
    ! [A_77,B_78] :
      ( u1_struct_0(k6_tmap_1(A_77,B_78)) = u1_struct_0(A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_533,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_530])).

tff(c_536,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_533])).

tff(c_537,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_536])).

tff(c_538,plain,(
    ! [A_79,B_80] :
      ( u1_pre_topc(k6_tmap_1(A_79,B_80)) = k5_tmap_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_541,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_538])).

tff(c_544,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_541])).

tff(c_545,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_544])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_593,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_2])).

tff(c_597,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_529,c_537,c_593])).

tff(c_698,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_597])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.70/1.43  
% 2.70/1.43  %Foreground sorts:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Background operators:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Foreground operators:
% 2.70/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.43  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.70/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.43  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.70/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.43  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.70/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.43  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.43  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.70/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.43  
% 3.12/1.45  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.12/1.45  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.12/1.45  tff(f_68, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.12/1.45  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.12/1.45  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 3.12/1.45  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 3.12/1.45  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.12/1.45  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.12/1.45  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.45  tff(c_56, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 3.12/1.45  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.45  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.45  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.45  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.45  tff(c_165, plain, (![A_37, B_38]: (u1_pre_topc(k6_tmap_1(A_37, B_38))=k5_tmap_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.45  tff(c_171, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_165])).
% 3.12/1.45  tff(c_176, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_171])).
% 3.12/1.45  tff(c_177, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_176])).
% 3.12/1.45  tff(c_105, plain, (![A_33, B_34]: (l1_pre_topc(k6_tmap_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.12/1.45  tff(c_108, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_105])).
% 3.12/1.45  tff(c_111, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_108])).
% 3.12/1.45  tff(c_112, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_111])).
% 3.12/1.45  tff(c_113, plain, (![A_35, B_36]: (u1_struct_0(k6_tmap_1(A_35, B_36))=u1_struct_0(A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.45  tff(c_116, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_113])).
% 3.12/1.45  tff(c_119, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_116])).
% 3.12/1.45  tff(c_120, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_119])).
% 3.12/1.45  tff(c_4, plain, (![B_4, A_2]: (v3_pre_topc(B_4, A_2) | ~r2_hidden(B_4, u1_pre_topc(A_2)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.45  tff(c_136, plain, (![B_4]: (v3_pre_topc(B_4, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_4, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_120, c_4])).
% 3.12/1.45  tff(c_154, plain, (![B_4]: (v3_pre_topc(B_4, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_4, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_136])).
% 3.12/1.45  tff(c_196, plain, (![B_39]: (v3_pre_topc(B_39, k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden(B_39, k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_154])).
% 3.12/1.45  tff(c_200, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_196])).
% 3.12/1.45  tff(c_201, plain, (~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_200])).
% 3.12/1.45  tff(c_6, plain, (![B_4, A_2]: (r2_hidden(B_4, u1_pre_topc(A_2)) | ~v3_pre_topc(B_4, A_2) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.45  tff(c_139, plain, (![B_4]: (r2_hidden(B_4, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~v3_pre_topc(B_4, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_120, c_6])).
% 3.12/1.45  tff(c_156, plain, (![B_4]: (r2_hidden(B_4, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~v3_pre_topc(B_4, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_139])).
% 3.12/1.45  tff(c_227, plain, (![B_43]: (r2_hidden(B_43, k5_tmap_1('#skF_1', '#skF_2')) | ~v3_pre_topc(B_43, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_156])).
% 3.12/1.45  tff(c_230, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_227])).
% 3.12/1.45  tff(c_233, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_201, c_230])).
% 3.12/1.45  tff(c_317, plain, (![C_50, A_51]: (v3_pre_topc(C_50, k6_tmap_1(A_51, C_50)) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_51, C_50)))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.12/1.45  tff(c_320, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_120, c_317])).
% 3.12/1.45  tff(c_322, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_32, c_320])).
% 3.12/1.45  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_233, c_322])).
% 3.12/1.45  tff(c_325, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_200])).
% 3.12/1.45  tff(c_46, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.12/1.45  tff(c_57, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_46])).
% 3.12/1.45  tff(c_450, plain, (![B_64, A_65]: (v3_pre_topc(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_65), u1_pre_topc(A_65))))) | ~v3_pre_topc(B_64, g1_pre_topc(u1_struct_0(A_65), u1_pre_topc(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.12/1.45  tff(c_462, plain, (![B_64]: (v3_pre_topc(B_64, '#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~v3_pre_topc(B_64, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_450])).
% 3.12/1.45  tff(c_473, plain, (![B_66]: (v3_pre_topc(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_66, k6_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_57, c_120, c_462])).
% 3.12/1.45  tff(c_476, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_473])).
% 3.12/1.45  tff(c_479, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_476])).
% 3.12/1.45  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_479])).
% 3.12/1.45  tff(c_482, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.12/1.45  tff(c_483, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 3.12/1.45  tff(c_499, plain, (![B_69, A_70]: (r2_hidden(B_69, u1_pre_topc(A_70)) | ~v3_pre_topc(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.45  tff(c_502, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_499])).
% 3.12/1.45  tff(c_505, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_483, c_502])).
% 3.12/1.45  tff(c_682, plain, (![A_90, B_91]: (k5_tmap_1(A_90, B_91)=u1_pre_topc(A_90) | ~r2_hidden(B_91, u1_pre_topc(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.12/1.45  tff(c_688, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_682])).
% 3.12/1.45  tff(c_693, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_505, c_688])).
% 3.12/1.45  tff(c_694, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_693])).
% 3.12/1.45  tff(c_514, plain, (![A_73, B_74]: (l1_pre_topc(k6_tmap_1(A_73, B_74)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.12/1.45  tff(c_517, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_514])).
% 3.12/1.45  tff(c_520, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_517])).
% 3.12/1.45  tff(c_521, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_520])).
% 3.12/1.45  tff(c_522, plain, (![A_75, B_76]: (v1_pre_topc(k6_tmap_1(A_75, B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.12/1.45  tff(c_525, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_522])).
% 3.12/1.45  tff(c_528, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_525])).
% 3.12/1.45  tff(c_529, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_528])).
% 3.12/1.45  tff(c_530, plain, (![A_77, B_78]: (u1_struct_0(k6_tmap_1(A_77, B_78))=u1_struct_0(A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.45  tff(c_533, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_530])).
% 3.12/1.45  tff(c_536, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_533])).
% 3.12/1.45  tff(c_537, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_536])).
% 3.12/1.45  tff(c_538, plain, (![A_79, B_80]: (u1_pre_topc(k6_tmap_1(A_79, B_80))=k5_tmap_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.45  tff(c_541, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_538])).
% 3.12/1.45  tff(c_544, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_541])).
% 3.12/1.45  tff(c_545, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_544])).
% 3.12/1.45  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.45  tff(c_593, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_545, c_2])).
% 3.12/1.45  tff(c_597, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_529, c_537, c_593])).
% 3.12/1.45  tff(c_698, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_694, c_597])).
% 3.12/1.45  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_482, c_698])).
% 3.12/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.45  
% 3.12/1.45  Inference rules
% 3.12/1.45  ----------------------
% 3.12/1.45  #Ref     : 0
% 3.12/1.45  #Sup     : 120
% 3.12/1.45  #Fact    : 0
% 3.12/1.45  #Define  : 0
% 3.12/1.45  #Split   : 8
% 3.12/1.45  #Chain   : 0
% 3.12/1.45  #Close   : 0
% 3.12/1.45  
% 3.12/1.45  Ordering : KBO
% 3.12/1.45  
% 3.12/1.45  Simplification rules
% 3.12/1.45  ----------------------
% 3.12/1.45  #Subsume      : 8
% 3.12/1.45  #Demod        : 249
% 3.12/1.45  #Tautology    : 66
% 3.12/1.45  #SimpNegUnit  : 26
% 3.12/1.45  #BackRed      : 11
% 3.12/1.45  
% 3.12/1.45  #Partial instantiations: 0
% 3.12/1.45  #Strategies tried      : 1
% 3.12/1.45  
% 3.12/1.45  Timing (in seconds)
% 3.12/1.45  ----------------------
% 3.12/1.46  Preprocessing        : 0.33
% 3.12/1.46  Parsing              : 0.18
% 3.12/1.46  CNF conversion       : 0.02
% 3.12/1.46  Main loop            : 0.33
% 3.12/1.46  Inferencing          : 0.11
% 3.12/1.46  Reduction            : 0.12
% 3.12/1.46  Demodulation         : 0.08
% 3.12/1.46  BG Simplification    : 0.02
% 3.12/1.46  Subsumption          : 0.06
% 3.12/1.46  Abstraction          : 0.02
% 3.12/1.46  MUC search           : 0.00
% 3.12/1.46  Cooper               : 0.00
% 3.12/1.46  Total                : 0.70
% 3.12/1.46  Index Insertion      : 0.00
% 3.12/1.46  Index Deletion       : 0.00
% 3.12/1.46  Index Matching       : 0.00
% 3.12/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
