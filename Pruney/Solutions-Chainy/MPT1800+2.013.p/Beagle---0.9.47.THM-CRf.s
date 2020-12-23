%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:59 EST 2020

% Result     : Theorem 50.39s
% Output     : CNFRefutation 50.39s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 382 expanded)
%              Number of leaves         :   31 ( 148 expanded)
%              Depth                    :   16
%              Number of atoms          :  414 (1546 expanded)
%              Number of equality atoms :   36 ( 192 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_108,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_65,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_75,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_22,plain,(
    ! [A_8,B_14] :
      ( m1_subset_1('#skF_1'(A_8,B_14),k1_zfmisc_1(u1_struct_0(A_8)))
      | v1_tsep_1(B_14,A_8)
      | ~ m1_pre_topc(B_14,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    ! [B_40,A_41] :
      ( u1_struct_0(B_40) = '#skF_1'(A_41,B_40)
      | v1_tsep_1(B_40,A_41)
      | ~ m1_pre_topc(B_40,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_75])).

tff(c_99,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_96])).

tff(c_40,plain,(
    ! [B_35,A_33] :
      ( m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_103,plain,(
    ! [A_33] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc('#skF_3',A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_40])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_77,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_62])).

tff(c_279,plain,(
    ! [B_75,A_76] :
      ( v3_pre_topc(B_75,g1_pre_topc(u1_struct_0(A_76),u1_pre_topc(A_76)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v3_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_292,plain,(
    ! [B_75] :
      ( v3_pre_topc(B_75,k8_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_75,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_279])).

tff(c_300,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,k8_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_77,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_292])).

tff(c_308,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_300])).

tff(c_318,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_308])).

tff(c_322,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_38,plain,(
    ! [A_26,B_30] :
      ( u1_struct_0(k8_tmap_1(A_26,B_30)) = u1_struct_0(A_26)
      | ~ m1_pre_topc(B_30,A_26)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_606,plain,(
    ! [B_104,A_105] :
      ( v3_pre_topc(B_104,A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)))))
      | ~ v3_pre_topc(B_104,g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_626,plain,(
    ! [B_104] :
      ( v3_pre_topc(B_104,'#skF_2')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))
      | ~ v3_pre_topc(B_104,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_606])).

tff(c_641,plain,(
    ! [B_106] :
      ( v3_pre_topc(B_106,'#skF_2')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))
      | ~ v3_pre_topc(B_106,k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_77,c_626])).

tff(c_647,plain,(
    ! [B_106] :
      ( v3_pre_topc(B_106,'#skF_2')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_106,k8_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_641])).

tff(c_662,plain,(
    ! [B_106] :
      ( v3_pre_topc(B_106,'#skF_2')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_106,k8_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_647])).

tff(c_675,plain,(
    ! [B_107] :
      ( v3_pre_topc(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_107,k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_662])).

tff(c_683,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_675])).

tff(c_693,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_683])).

tff(c_694,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_322,c_693])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( l1_pre_topc(k8_tmap_1(A_18,B_19))
      | ~ m1_pre_topc(B_19,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_451,plain,(
    ! [B_93,A_94] :
      ( m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)))))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v3_pre_topc(B_93,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_474,plain,(
    ! [B_93] :
      ( m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_93,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_451])).

tff(c_486,plain,(
    ! [B_95] :
      ( m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_95,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_474])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ v3_pre_topc(B_4,A_2)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_507,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')))
      | ~ v3_pre_topc(B_95,k8_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_95,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_486,c_6])).

tff(c_540,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_543,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_540])).

tff(c_546,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_543])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_546])).

tff(c_550,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_1016,plain,(
    ! [A_122,B_123] :
      ( k5_tmap_1(A_122,u1_struct_0(B_123)) = u1_pre_topc(k8_tmap_1(A_122,B_123))
      | ~ m1_subset_1(u1_struct_0(B_123),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_pre_topc(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1055,plain,(
    ! [A_124,B_125] :
      ( k5_tmap_1(A_124,u1_struct_0(B_125)) = u1_pre_topc(k8_tmap_1(A_124,B_125))
      | v2_struct_0(B_125)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124)
      | ~ m1_pre_topc(B_125,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_40,c_1016])).

tff(c_1080,plain,(
    ! [A_124] :
      ( k5_tmap_1(A_124,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_124,'#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124)
      | ~ m1_pre_topc('#skF_3',A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1055])).

tff(c_1087,plain,(
    ! [A_126] :
      ( k5_tmap_1(A_126,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_126,'#skF_3'))
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126)
      | ~ m1_pre_topc('#skF_3',A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1080])).

tff(c_172,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,k5_tmap_1(A_62,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_181,plain,(
    ! [A_8,B_14] :
      ( r2_hidden('#skF_1'(A_8,B_14),k5_tmap_1(A_8,'#skF_1'(A_8,B_14)))
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8)
      | v1_tsep_1(B_14,A_8)
      | ~ m1_pre_topc(B_14,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_172])).

tff(c_1094,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_181])).

tff(c_1109,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')))
    | v1_tsep_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_48,c_46,c_42,c_48,c_1094])).

tff(c_1110,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_75,c_1109])).

tff(c_200,plain,(
    ! [A_67,B_68] :
      ( u1_struct_0(k8_tmap_1(A_67,B_68)) = u1_struct_0(A_67)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v3_pre_topc(B_4,A_2)
      | ~ r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2570,plain,(
    ! [B_225,A_226,B_227] :
      ( v3_pre_topc(B_225,k8_tmap_1(A_226,B_227))
      | ~ r2_hidden(B_225,u1_pre_topc(k8_tmap_1(A_226,B_227)))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(k8_tmap_1(A_226,B_227))
      | ~ m1_pre_topc(B_227,A_226)
      | v2_struct_0(B_227)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_4])).

tff(c_2603,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1110,c_2570])).

tff(c_2634,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_550,c_2603])).

tff(c_2635,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_694,c_2634])).

tff(c_2645,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2635])).

tff(c_2651,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2645])).

tff(c_2653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2651])).

tff(c_2655,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_18,plain,(
    ! [A_8,B_14] :
      ( ~ v3_pre_topc('#skF_1'(A_8,B_14),A_8)
      | v1_tsep_1(B_14,A_8)
      | ~ m1_pre_topc(B_14,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2658,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2655,c_18])).

tff(c_2661,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2658])).

tff(c_2663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2661])).

tff(c_2664,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_2665,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( v1_pre_topc(k8_tmap_1(A_18,B_19))
      | ~ m1_pre_topc(B_19,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2952,plain,(
    ! [A_291,B_292] :
      ( k5_tmap_1(A_291,u1_struct_0(B_292)) = u1_pre_topc(k8_tmap_1(A_291,B_292))
      | ~ m1_subset_1(u1_struct_0(B_292),k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ m1_pre_topc(B_292,A_291)
      | v2_struct_0(B_292)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2968,plain,(
    ! [A_293,B_294] :
      ( k5_tmap_1(A_293,u1_struct_0(B_294)) = u1_pre_topc(k8_tmap_1(A_293,B_294))
      | v2_struct_0(B_294)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293)
      | ~ m1_pre_topc(B_294,A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(resolution,[status(thm)],[c_40,c_2952])).

tff(c_2753,plain,(
    ! [B_256,A_257] :
      ( v3_pre_topc(u1_struct_0(B_256),A_257)
      | ~ m1_subset_1(u1_struct_0(B_256),k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v1_tsep_1(B_256,A_257)
      | ~ m1_pre_topc(B_256,A_257)
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2763,plain,(
    ! [B_35,A_33] :
      ( v3_pre_topc(u1_struct_0(B_35),A_33)
      | ~ v1_tsep_1(B_35,A_33)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_40,c_2753])).

tff(c_2684,plain,(
    ! [B_242,A_243] :
      ( r2_hidden(B_242,u1_pre_topc(A_243))
      | ~ v3_pre_topc(B_242,A_243)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2688,plain,(
    ! [B_35,A_33] :
      ( r2_hidden(u1_struct_0(B_35),u1_pre_topc(A_33))
      | ~ v3_pre_topc(u1_struct_0(B_35),A_33)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_40,c_2684])).

tff(c_2793,plain,(
    ! [A_266,B_267] :
      ( k5_tmap_1(A_266,B_267) = u1_pre_topc(A_266)
      | ~ r2_hidden(B_267,u1_pre_topc(A_266))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2843,plain,(
    ! [A_274,B_275] :
      ( k5_tmap_1(A_274,u1_struct_0(B_275)) = u1_pre_topc(A_274)
      | ~ r2_hidden(u1_struct_0(B_275),u1_pre_topc(A_274))
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274)
      | ~ m1_pre_topc(B_275,A_274)
      | ~ l1_pre_topc(A_274) ) ),
    inference(resolution,[status(thm)],[c_40,c_2793])).

tff(c_2855,plain,(
    ! [A_276,B_277] :
      ( k5_tmap_1(A_276,u1_struct_0(B_277)) = u1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276)
      | ~ v3_pre_topc(u1_struct_0(B_277),A_276)
      | ~ m1_pre_topc(B_277,A_276)
      | ~ l1_pre_topc(A_276) ) ),
    inference(resolution,[status(thm)],[c_2688,c_2843])).

tff(c_2871,plain,(
    ! [A_33,B_35] :
      ( k5_tmap_1(A_33,u1_struct_0(B_35)) = u1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33)
      | ~ v1_tsep_1(B_35,A_33)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_2763,c_2855])).

tff(c_3151,plain,(
    ! [A_332,B_333] :
      ( u1_pre_topc(k8_tmap_1(A_332,B_333)) = u1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332)
      | ~ v1_tsep_1(B_333,A_332)
      | ~ m1_pre_topc(B_333,A_332)
      | ~ l1_pre_topc(A_332)
      | v2_struct_0(B_333)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332)
      | ~ m1_pre_topc(B_333,A_332)
      | ~ l1_pre_topc(A_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2968,c_2871])).

tff(c_2711,plain,(
    ! [A_252,B_253] :
      ( u1_struct_0(k8_tmap_1(A_252,B_253)) = u1_struct_0(A_252)
      | ~ m1_pre_topc(B_253,A_252)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2740,plain,(
    ! [A_252,B_253] :
      ( g1_pre_topc(u1_struct_0(A_252),u1_pre_topc(k8_tmap_1(A_252,B_253))) = k8_tmap_1(A_252,B_253)
      | ~ v1_pre_topc(k8_tmap_1(A_252,B_253))
      | ~ l1_pre_topc(k8_tmap_1(A_252,B_253))
      | ~ m1_pre_topc(B_253,A_252)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2711,c_2])).

tff(c_40799,plain,(
    ! [A_1373,B_1374] :
      ( k8_tmap_1(A_1373,B_1374) = g1_pre_topc(u1_struct_0(A_1373),u1_pre_topc(A_1373))
      | ~ v1_pre_topc(k8_tmap_1(A_1373,B_1374))
      | ~ l1_pre_topc(k8_tmap_1(A_1373,B_1374))
      | ~ m1_pre_topc(B_1374,A_1373)
      | v2_struct_0(B_1374)
      | ~ l1_pre_topc(A_1373)
      | ~ v2_pre_topc(A_1373)
      | v2_struct_0(A_1373)
      | ~ v2_pre_topc(A_1373)
      | v2_struct_0(A_1373)
      | ~ v1_tsep_1(B_1374,A_1373)
      | ~ m1_pre_topc(B_1374,A_1373)
      | ~ l1_pre_topc(A_1373)
      | v2_struct_0(B_1374)
      | ~ v2_pre_topc(A_1373)
      | v2_struct_0(A_1373)
      | ~ m1_pre_topc(B_1374,A_1373)
      | ~ l1_pre_topc(A_1373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3151,c_2740])).

tff(c_40803,plain,(
    ! [A_1375,B_1376] :
      ( k8_tmap_1(A_1375,B_1376) = g1_pre_topc(u1_struct_0(A_1375),u1_pre_topc(A_1375))
      | ~ l1_pre_topc(k8_tmap_1(A_1375,B_1376))
      | ~ v1_tsep_1(B_1376,A_1375)
      | v2_struct_0(B_1376)
      | ~ m1_pre_topc(B_1376,A_1375)
      | ~ l1_pre_topc(A_1375)
      | ~ v2_pre_topc(A_1375)
      | v2_struct_0(A_1375) ) ),
    inference(resolution,[status(thm)],[c_28,c_40799])).

tff(c_40807,plain,(
    ! [A_1377,B_1378] :
      ( k8_tmap_1(A_1377,B_1378) = g1_pre_topc(u1_struct_0(A_1377),u1_pre_topc(A_1377))
      | ~ v1_tsep_1(B_1378,A_1377)
      | v2_struct_0(B_1378)
      | ~ m1_pre_topc(B_1378,A_1377)
      | ~ l1_pre_topc(A_1377)
      | ~ v2_pre_topc(A_1377)
      | v2_struct_0(A_1377) ) ),
    inference(resolution,[status(thm)],[c_24,c_40803])).

tff(c_40813,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2665,c_40807])).

tff(c_40818,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40813])).

tff(c_40820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_2664,c_40818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:08 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.39/38.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.39/38.75  
% 50.39/38.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.39/38.75  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 50.39/38.75  
% 50.39/38.75  %Foreground sorts:
% 50.39/38.75  
% 50.39/38.75  
% 50.39/38.75  %Background operators:
% 50.39/38.75  
% 50.39/38.75  
% 50.39/38.75  %Foreground operators:
% 50.39/38.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 50.39/38.75  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 50.39/38.75  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 50.39/38.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.39/38.75  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 50.39/38.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.39/38.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 50.39/38.75  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 50.39/38.75  tff('#skF_2', type, '#skF_2': $i).
% 50.39/38.75  tff('#skF_3', type, '#skF_3': $i).
% 50.39/38.75  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 50.39/38.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 50.39/38.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.39/38.75  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 50.39/38.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.39/38.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 50.39/38.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 50.39/38.75  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 50.39/38.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 50.39/38.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 50.39/38.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 50.39/38.75  
% 50.39/38.78  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 50.39/38.78  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 50.39/38.78  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 50.39/38.78  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 50.39/38.78  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 50.39/38.78  tff(f_82, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 50.39/38.78  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 50.39/38.78  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 50.39/38.78  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 50.39/38.78  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 50.39/38.78  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_65, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 50.39/38.78  tff(c_75, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_65])).
% 50.39/38.78  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_22, plain, (![A_8, B_14]: (m1_subset_1('#skF_1'(A_8, B_14), k1_zfmisc_1(u1_struct_0(A_8))) | v1_tsep_1(B_14, A_8) | ~m1_pre_topc(B_14, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_67])).
% 50.39/38.78  tff(c_93, plain, (![B_40, A_41]: (u1_struct_0(B_40)='#skF_1'(A_41, B_40) | v1_tsep_1(B_40, A_41) | ~m1_pre_topc(B_40, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 50.39/38.78  tff(c_96, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_93, c_75])).
% 50.39/38.78  tff(c_99, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_96])).
% 50.39/38.78  tff(c_40, plain, (![B_35, A_33]: (m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_137])).
% 50.39/38.78  tff(c_103, plain, (![A_33]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc('#skF_3', A_33) | ~l1_pre_topc(A_33))), inference(superposition, [status(thm), theory('equality')], [c_99, c_40])).
% 50.39/38.78  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_62, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 50.39/38.78  tff(c_77, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_75, c_62])).
% 50.39/38.78  tff(c_279, plain, (![B_75, A_76]: (v3_pre_topc(B_75, g1_pre_topc(u1_struct_0(A_76), u1_pre_topc(A_76))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~v3_pre_topc(B_75, A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_53])).
% 50.39/38.78  tff(c_292, plain, (![B_75]: (v3_pre_topc(B_75, k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_75, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_279])).
% 50.39/38.78  tff(c_300, plain, (![B_77]: (v3_pre_topc(B_77, k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_77, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_292])).
% 50.39/38.78  tff(c_308, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_103, c_300])).
% 50.39/38.78  tff(c_318, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_308])).
% 50.39/38.78  tff(c_322, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_318])).
% 50.39/38.78  tff(c_38, plain, (![A_26, B_30]: (u1_struct_0(k8_tmap_1(A_26, B_30))=u1_struct_0(A_26) | ~m1_pre_topc(B_30, A_26) | v2_struct_0(B_30) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_130])).
% 50.39/38.78  tff(c_606, plain, (![B_104, A_105]: (v3_pre_topc(B_104, A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))))) | ~v3_pre_topc(B_104, g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_53])).
% 50.39/38.78  tff(c_626, plain, (![B_104]: (v3_pre_topc(B_104, '#skF_2') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))) | ~v3_pre_topc(B_104, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_606])).
% 50.39/38.78  tff(c_641, plain, (![B_106]: (v3_pre_topc(B_106, '#skF_2') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))) | ~v3_pre_topc(B_106, k8_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_77, c_626])).
% 50.39/38.78  tff(c_647, plain, (![B_106]: (v3_pre_topc(B_106, '#skF_2') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_106, k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_641])).
% 50.39/38.78  tff(c_662, plain, (![B_106]: (v3_pre_topc(B_106, '#skF_2') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_106, k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_647])).
% 50.39/38.78  tff(c_675, plain, (![B_107]: (v3_pre_topc(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_107, k8_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_662])).
% 50.39/38.78  tff(c_683, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_103, c_675])).
% 50.39/38.78  tff(c_693, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_683])).
% 50.39/38.78  tff(c_694, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_322, c_693])).
% 50.39/38.78  tff(c_24, plain, (![A_18, B_19]: (l1_pre_topc(k8_tmap_1(A_18, B_19)) | ~m1_pre_topc(B_19, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 50.39/38.78  tff(c_451, plain, (![B_93, A_94]: (m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94))))) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~v3_pre_topc(B_93, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 50.39/38.78  tff(c_474, plain, (![B_93]: (m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_93, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_451])).
% 50.39/38.78  tff(c_486, plain, (![B_95]: (m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_95, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_474])).
% 50.39/38.78  tff(c_6, plain, (![B_4, A_2]: (r2_hidden(B_4, u1_pre_topc(A_2)) | ~v3_pre_topc(B_4, A_2) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 50.39/38.78  tff(c_507, plain, (![B_95]: (r2_hidden(B_95, u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))) | ~v3_pre_topc(B_95, k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_95, '#skF_2'))), inference(resolution, [status(thm)], [c_486, c_6])).
% 50.39/38.78  tff(c_540, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_507])).
% 50.39/38.78  tff(c_543, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_540])).
% 50.39/38.78  tff(c_546, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_543])).
% 50.39/38.78  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_546])).
% 50.39/38.78  tff(c_550, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_507])).
% 50.39/38.78  tff(c_1016, plain, (![A_122, B_123]: (k5_tmap_1(A_122, u1_struct_0(B_123))=u1_pre_topc(k8_tmap_1(A_122, B_123)) | ~m1_subset_1(u1_struct_0(B_123), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_pre_topc(B_123, A_122) | v2_struct_0(B_123) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_130])).
% 50.39/38.78  tff(c_1055, plain, (![A_124, B_125]: (k5_tmap_1(A_124, u1_struct_0(B_125))=u1_pre_topc(k8_tmap_1(A_124, B_125)) | v2_struct_0(B_125) | ~v2_pre_topc(A_124) | v2_struct_0(A_124) | ~m1_pre_topc(B_125, A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_40, c_1016])).
% 50.39/38.78  tff(c_1080, plain, (![A_124]: (k5_tmap_1(A_124, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_124, '#skF_3')) | v2_struct_0('#skF_3') | ~v2_pre_topc(A_124) | v2_struct_0(A_124) | ~m1_pre_topc('#skF_3', A_124) | ~l1_pre_topc(A_124))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1055])).
% 50.39/38.78  tff(c_1087, plain, (![A_126]: (k5_tmap_1(A_126, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_126, '#skF_3')) | ~v2_pre_topc(A_126) | v2_struct_0(A_126) | ~m1_pre_topc('#skF_3', A_126) | ~l1_pre_topc(A_126))), inference(negUnitSimplification, [status(thm)], [c_44, c_1080])).
% 50.39/38.78  tff(c_172, plain, (![B_61, A_62]: (r2_hidden(B_61, k5_tmap_1(A_62, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 50.39/38.78  tff(c_181, plain, (![A_8, B_14]: (r2_hidden('#skF_1'(A_8, B_14), k5_tmap_1(A_8, '#skF_1'(A_8, B_14))) | ~v2_pre_topc(A_8) | v2_struct_0(A_8) | v1_tsep_1(B_14, A_8) | ~m1_pre_topc(B_14, A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_22, c_172])).
% 50.39/38.78  tff(c_1094, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1087, c_181])).
% 50.39/38.78  tff(c_1109, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))) | v1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_48, c_46, c_42, c_48, c_1094])).
% 50.39/38.78  tff(c_1110, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_75, c_1109])).
% 50.39/38.78  tff(c_200, plain, (![A_67, B_68]: (u1_struct_0(k8_tmap_1(A_67, B_68))=u1_struct_0(A_67) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_130])).
% 50.39/38.78  tff(c_4, plain, (![B_4, A_2]: (v3_pre_topc(B_4, A_2) | ~r2_hidden(B_4, u1_pre_topc(A_2)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 50.39/38.78  tff(c_2570, plain, (![B_225, A_226, B_227]: (v3_pre_topc(B_225, k8_tmap_1(A_226, B_227)) | ~r2_hidden(B_225, u1_pre_topc(k8_tmap_1(A_226, B_227))) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(k8_tmap_1(A_226, B_227)) | ~m1_pre_topc(B_227, A_226) | v2_struct_0(B_227) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(superposition, [status(thm), theory('equality')], [c_200, c_4])).
% 50.39/38.78  tff(c_2603, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1110, c_2570])).
% 50.39/38.78  tff(c_2634, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_550, c_2603])).
% 50.39/38.78  tff(c_2635, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_694, c_2634])).
% 50.39/38.78  tff(c_2645, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2635])).
% 50.39/38.78  tff(c_2651, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2645])).
% 50.39/38.78  tff(c_2653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_2651])).
% 50.39/38.78  tff(c_2655, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_318])).
% 50.39/38.78  tff(c_18, plain, (![A_8, B_14]: (~v3_pre_topc('#skF_1'(A_8, B_14), A_8) | v1_tsep_1(B_14, A_8) | ~m1_pre_topc(B_14, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_67])).
% 50.39/38.78  tff(c_2658, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2655, c_18])).
% 50.39/38.78  tff(c_2661, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2658])).
% 50.39/38.78  tff(c_2663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_2661])).
% 50.39/38.78  tff(c_2664, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_65])).
% 50.39/38.78  tff(c_2665, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_65])).
% 50.39/38.78  tff(c_28, plain, (![A_18, B_19]: (v1_pre_topc(k8_tmap_1(A_18, B_19)) | ~m1_pre_topc(B_19, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 50.39/38.78  tff(c_2952, plain, (![A_291, B_292]: (k5_tmap_1(A_291, u1_struct_0(B_292))=u1_pre_topc(k8_tmap_1(A_291, B_292)) | ~m1_subset_1(u1_struct_0(B_292), k1_zfmisc_1(u1_struct_0(A_291))) | ~m1_pre_topc(B_292, A_291) | v2_struct_0(B_292) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_130])).
% 50.39/38.78  tff(c_2968, plain, (![A_293, B_294]: (k5_tmap_1(A_293, u1_struct_0(B_294))=u1_pre_topc(k8_tmap_1(A_293, B_294)) | v2_struct_0(B_294) | ~v2_pre_topc(A_293) | v2_struct_0(A_293) | ~m1_pre_topc(B_294, A_293) | ~l1_pre_topc(A_293))), inference(resolution, [status(thm)], [c_40, c_2952])).
% 50.39/38.78  tff(c_2753, plain, (![B_256, A_257]: (v3_pre_topc(u1_struct_0(B_256), A_257) | ~m1_subset_1(u1_struct_0(B_256), k1_zfmisc_1(u1_struct_0(A_257))) | ~v1_tsep_1(B_256, A_257) | ~m1_pre_topc(B_256, A_257) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_67])).
% 50.39/38.78  tff(c_2763, plain, (![B_35, A_33]: (v3_pre_topc(u1_struct_0(B_35), A_33) | ~v1_tsep_1(B_35, A_33) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_40, c_2753])).
% 50.39/38.78  tff(c_2684, plain, (![B_242, A_243]: (r2_hidden(B_242, u1_pre_topc(A_243)) | ~v3_pre_topc(B_242, A_243) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_40])).
% 50.39/38.78  tff(c_2688, plain, (![B_35, A_33]: (r2_hidden(u1_struct_0(B_35), u1_pre_topc(A_33)) | ~v3_pre_topc(u1_struct_0(B_35), A_33) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_40, c_2684])).
% 50.39/38.78  tff(c_2793, plain, (![A_266, B_267]: (k5_tmap_1(A_266, B_267)=u1_pre_topc(A_266) | ~r2_hidden(B_267, u1_pre_topc(A_266)) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_108])).
% 50.39/38.78  tff(c_2843, plain, (![A_274, B_275]: (k5_tmap_1(A_274, u1_struct_0(B_275))=u1_pre_topc(A_274) | ~r2_hidden(u1_struct_0(B_275), u1_pre_topc(A_274)) | ~v2_pre_topc(A_274) | v2_struct_0(A_274) | ~m1_pre_topc(B_275, A_274) | ~l1_pre_topc(A_274))), inference(resolution, [status(thm)], [c_40, c_2793])).
% 50.39/38.78  tff(c_2855, plain, (![A_276, B_277]: (k5_tmap_1(A_276, u1_struct_0(B_277))=u1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276) | ~v3_pre_topc(u1_struct_0(B_277), A_276) | ~m1_pre_topc(B_277, A_276) | ~l1_pre_topc(A_276))), inference(resolution, [status(thm)], [c_2688, c_2843])).
% 50.39/38.78  tff(c_2871, plain, (![A_33, B_35]: (k5_tmap_1(A_33, u1_struct_0(B_35))=u1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33) | ~v1_tsep_1(B_35, A_33) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_2763, c_2855])).
% 50.39/38.78  tff(c_3151, plain, (![A_332, B_333]: (u1_pre_topc(k8_tmap_1(A_332, B_333))=u1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332) | ~v1_tsep_1(B_333, A_332) | ~m1_pre_topc(B_333, A_332) | ~l1_pre_topc(A_332) | v2_struct_0(B_333) | ~v2_pre_topc(A_332) | v2_struct_0(A_332) | ~m1_pre_topc(B_333, A_332) | ~l1_pre_topc(A_332))), inference(superposition, [status(thm), theory('equality')], [c_2968, c_2871])).
% 50.39/38.78  tff(c_2711, plain, (![A_252, B_253]: (u1_struct_0(k8_tmap_1(A_252, B_253))=u1_struct_0(A_252) | ~m1_pre_topc(B_253, A_252) | v2_struct_0(B_253) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_130])).
% 50.39/38.78  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 50.39/38.78  tff(c_2740, plain, (![A_252, B_253]: (g1_pre_topc(u1_struct_0(A_252), u1_pre_topc(k8_tmap_1(A_252, B_253)))=k8_tmap_1(A_252, B_253) | ~v1_pre_topc(k8_tmap_1(A_252, B_253)) | ~l1_pre_topc(k8_tmap_1(A_252, B_253)) | ~m1_pre_topc(B_253, A_252) | v2_struct_0(B_253) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(superposition, [status(thm), theory('equality')], [c_2711, c_2])).
% 50.39/38.78  tff(c_40799, plain, (![A_1373, B_1374]: (k8_tmap_1(A_1373, B_1374)=g1_pre_topc(u1_struct_0(A_1373), u1_pre_topc(A_1373)) | ~v1_pre_topc(k8_tmap_1(A_1373, B_1374)) | ~l1_pre_topc(k8_tmap_1(A_1373, B_1374)) | ~m1_pre_topc(B_1374, A_1373) | v2_struct_0(B_1374) | ~l1_pre_topc(A_1373) | ~v2_pre_topc(A_1373) | v2_struct_0(A_1373) | ~v2_pre_topc(A_1373) | v2_struct_0(A_1373) | ~v1_tsep_1(B_1374, A_1373) | ~m1_pre_topc(B_1374, A_1373) | ~l1_pre_topc(A_1373) | v2_struct_0(B_1374) | ~v2_pre_topc(A_1373) | v2_struct_0(A_1373) | ~m1_pre_topc(B_1374, A_1373) | ~l1_pre_topc(A_1373))), inference(superposition, [status(thm), theory('equality')], [c_3151, c_2740])).
% 50.39/38.78  tff(c_40803, plain, (![A_1375, B_1376]: (k8_tmap_1(A_1375, B_1376)=g1_pre_topc(u1_struct_0(A_1375), u1_pre_topc(A_1375)) | ~l1_pre_topc(k8_tmap_1(A_1375, B_1376)) | ~v1_tsep_1(B_1376, A_1375) | v2_struct_0(B_1376) | ~m1_pre_topc(B_1376, A_1375) | ~l1_pre_topc(A_1375) | ~v2_pre_topc(A_1375) | v2_struct_0(A_1375))), inference(resolution, [status(thm)], [c_28, c_40799])).
% 50.39/38.78  tff(c_40807, plain, (![A_1377, B_1378]: (k8_tmap_1(A_1377, B_1378)=g1_pre_topc(u1_struct_0(A_1377), u1_pre_topc(A_1377)) | ~v1_tsep_1(B_1378, A_1377) | v2_struct_0(B_1378) | ~m1_pre_topc(B_1378, A_1377) | ~l1_pre_topc(A_1377) | ~v2_pre_topc(A_1377) | v2_struct_0(A_1377))), inference(resolution, [status(thm)], [c_24, c_40803])).
% 50.39/38.78  tff(c_40813, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2665, c_40807])).
% 50.39/38.78  tff(c_40818, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40813])).
% 50.39/38.78  tff(c_40820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_2664, c_40818])).
% 50.39/38.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.39/38.78  
% 50.39/38.78  Inference rules
% 50.39/38.78  ----------------------
% 50.39/38.78  #Ref     : 0
% 50.39/38.78  #Sup     : 12783
% 50.39/38.78  #Fact    : 0
% 50.39/38.78  #Define  : 0
% 50.39/38.78  #Split   : 9
% 50.39/38.78  #Chain   : 0
% 50.39/38.78  #Close   : 0
% 50.39/38.78  
% 50.39/38.78  Ordering : KBO
% 50.39/38.78  
% 50.39/38.78  Simplification rules
% 50.39/38.78  ----------------------
% 50.39/38.78  #Subsume      : 2722
% 50.39/38.78  #Demod        : 457
% 50.39/38.78  #Tautology    : 939
% 50.39/38.78  #SimpNegUnit  : 114
% 50.39/38.78  #BackRed      : 0
% 50.39/38.78  
% 50.39/38.78  #Partial instantiations: 0
% 50.39/38.78  #Strategies tried      : 1
% 50.39/38.78  
% 50.39/38.78  Timing (in seconds)
% 50.39/38.78  ----------------------
% 50.39/38.78  Preprocessing        : 0.38
% 50.39/38.78  Parsing              : 0.21
% 50.39/38.78  CNF conversion       : 0.02
% 50.39/38.78  Main loop            : 37.51
% 50.39/38.78  Inferencing          : 3.14
% 50.39/38.78  Reduction            : 2.94
% 50.39/38.78  Demodulation         : 2.01
% 50.39/38.78  BG Simplification    : 0.57
% 50.39/38.78  Subsumption          : 30.22
% 50.39/38.78  Abstraction          : 0.70
% 50.39/38.78  MUC search           : 0.00
% 50.39/38.78  Cooper               : 0.00
% 50.39/38.78  Total                : 37.94
% 50.39/38.78  Index Insertion      : 0.00
% 50.39/38.78  Index Deletion       : 0.00
% 50.39/38.78  Index Matching       : 0.00
% 50.39/38.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
