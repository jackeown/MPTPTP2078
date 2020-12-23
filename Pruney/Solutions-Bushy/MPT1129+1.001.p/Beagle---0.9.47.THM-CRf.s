%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1129+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:27 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :  248 (1190 expanded)
%              Number of leaves         :   23 ( 352 expanded)
%              Depth                    :   17
%              Number of atoms          :  500 (3309 expanded)
%              Number of equality atoms :   92 ( 280 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v3_pre_topc(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_25,C_26,B_27] :
      ( m1_subset_1(A_25,C_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(C_26))
      | ~ r2_hidden(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    ! [A_25,A_7] :
      ( m1_subset_1(A_25,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ r2_hidden(A_25,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_56])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_118,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,u1_pre_topc(A_48))
      | ~ v3_pre_topc(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_79,c_118])).

tff(c_127,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_52,c_121])).

tff(c_43,plain,(
    ! [A_22] :
      ( m1_subset_1(u1_pre_topc(A_22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( l1_pre_topc(g1_pre_topc(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [A_22] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_43,c_8])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_pre_topc(g1_pre_topc(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_22] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_43,c_10])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_89,plain,(
    ! [D_32,B_33,C_34,A_35] :
      ( D_32 = B_33
      | g1_pre_topc(C_34,D_32) != g1_pre_topc(A_35,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,(
    ! [A_1,B_33,A_35] :
      ( u1_pre_topc(A_1) = B_33
      | g1_pre_topc(A_35,B_33) != A_1
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_35)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_181,plain,(
    ! [A_62,B_63] :
      ( u1_pre_topc(g1_pre_topc(A_62,B_63)) = B_63
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62)))
      | ~ v1_pre_topc(g1_pre_topc(A_62,B_63))
      | ~ l1_pre_topc(g1_pre_topc(A_62,B_63)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_91])).

tff(c_191,plain,(
    ! [A_66] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_66),u1_pre_topc(A_66))) = u1_pre_topc(A_66)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_66),u1_pre_topc(A_66)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_66),u1_pre_topc(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_12,c_181])).

tff(c_207,plain,(
    ! [A_68] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_68),u1_pre_topc(A_68))) = u1_pre_topc(A_68)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_68),u1_pre_topc(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_51,c_191])).

tff(c_215,plain,(
    ! [A_69] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_69),u1_pre_topc(A_69))) = u1_pre_topc(A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_50,c_207])).

tff(c_106,plain,(
    ! [B_43,A_44] :
      ( v3_pre_topc(B_43,A_44)
      | ~ r2_hidden(B_43,u1_pre_topc(A_44))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [A_25,A_7] :
      ( v3_pre_topc(A_25,A_7)
      | ~ r2_hidden(A_25,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_59,c_106])).

tff(c_514,plain,(
    ! [A_87,A_88] :
      ( v3_pre_topc(A_87,g1_pre_topc(u1_struct_0(A_88),u1_pre_topc(A_88)))
      | ~ r2_hidden(A_87,u1_pre_topc(A_88))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_88),u1_pre_topc(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_116])).

tff(c_28,plain,
    ( v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_129,plain,(
    ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_517,plain,
    ( ~ r2_hidden('#skF_3',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_514,c_129])).

tff(c_529,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_127,c_517])).

tff(c_535,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_529])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_535])).

tff(c_542,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_578,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_588,plain,
    ( ~ r2_hidden('#skF_3',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_59,c_578])).

tff(c_591,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_597,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_591])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_597])).

tff(c_605,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_648,plain,(
    ! [A_102,B_103] :
      ( u1_pre_topc(g1_pre_topc(A_102,B_103)) = B_103
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_102)))
      | ~ v1_pre_topc(g1_pre_topc(A_102,B_103))
      | ~ l1_pre_topc(g1_pre_topc(A_102,B_103)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_91])).

tff(c_658,plain,(
    ! [A_106] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106))) = u1_pre_topc(A_106)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_12,c_648])).

tff(c_685,plain,(
    ! [A_111] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_111),u1_pre_topc(A_111))) = u1_pre_topc(A_111)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_111),u1_pre_topc(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_51,c_658])).

tff(c_688,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_605,c_685])).

tff(c_697,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_688])).

tff(c_604,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_699,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_604])).

tff(c_702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_699])).

tff(c_704,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_24,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_544,plain,(
    ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_543,plain,(
    v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_543])).

tff(c_560,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_747,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_560])).

tff(c_748,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_747])).

tff(c_751,plain,
    ( ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_748])).

tff(c_754,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_751])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ v3_pre_topc(B_4,A_2)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_734,plain,
    ( r2_hidden('#skF_3',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_704,c_6])).

tff(c_742,plain,
    ( r2_hidden('#skF_3',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_734])).

tff(c_783,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_742])).

tff(c_789,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_783])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_789])).

tff(c_797,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_878,plain,(
    ! [A_128,B_129] :
      ( u1_pre_topc(g1_pre_topc(A_128,B_129)) = B_129
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k1_zfmisc_1(A_128)))
      | ~ v1_pre_topc(g1_pre_topc(A_128,B_129))
      | ~ l1_pre_topc(g1_pre_topc(A_128,B_129)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_91])).

tff(c_888,plain,(
    ! [A_132] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132))) = u1_pre_topc(A_132)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_12,c_878])).

tff(c_896,plain,(
    ! [A_133] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_133),u1_pre_topc(A_133))) = u1_pre_topc(A_133)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_133),u1_pre_topc(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_51,c_888])).

tff(c_899,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_797,c_896])).

tff(c_908,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_899])).

tff(c_703,plain,(
    v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_26,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_706,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_26])).

tff(c_707,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_704])).

tff(c_724,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_757,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_724,c_6])).

tff(c_765,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_757])).

tff(c_804,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_765])).

tff(c_913,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_804])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_913])).

tff(c_917,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_747])).

tff(c_932,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_724,c_6])).

tff(c_940,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_932])).

tff(c_956,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_962,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_956])).

tff(c_968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_962])).

tff(c_970,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_100,plain,(
    ! [C_36,A_37,D_38,B_39] :
      ( C_36 = A_37
      | g1_pre_topc(C_36,D_38) != g1_pre_topc(A_37,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [A_1,A_37,B_39] :
      ( u1_struct_0(A_1) = A_37
      | g1_pre_topc(A_37,B_39) != A_1
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_37)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_1050,plain,(
    ! [A_151,B_152] :
      ( u1_struct_0(g1_pre_topc(A_151,B_152)) = A_151
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k1_zfmisc_1(A_151)))
      | ~ v1_pre_topc(g1_pre_topc(A_151,B_152))
      | ~ l1_pre_topc(g1_pre_topc(A_151,B_152)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_102])).

tff(c_1060,plain,(
    ! [A_155] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_155),u1_pre_topc(A_155))) = u1_struct_0(A_155)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_155),u1_pre_topc(A_155)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_155),u1_pre_topc(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_12,c_1050])).

tff(c_1068,plain,(
    ! [A_156] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_156),u1_pre_topc(A_156))) = u1_struct_0(A_156)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_156),u1_pre_topc(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_51,c_1060])).

tff(c_1071,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_970,c_1068])).

tff(c_1080,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1071])).

tff(c_1109,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_12])).

tff(c_1128,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1109])).

tff(c_93,plain,(
    ! [A_1,D_32,C_34] :
      ( u1_pre_topc(A_1) = D_32
      | g1_pre_topc(C_34,D_32) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_1325,plain,(
    ! [C_163,D_164] :
      ( u1_pre_topc(g1_pre_topc(C_163,D_164)) = D_164
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_163,D_164)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_163,D_164)))))
      | ~ v1_pre_topc(g1_pre_topc(C_163,D_164))
      | ~ l1_pre_topc(g1_pre_topc(C_163,D_164)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_93])).

tff(c_1334,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_1325])).

tff(c_1347,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1128,c_1334])).

tff(c_1363,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1347])).

tff(c_1369,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_1363])).

tff(c_1375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1369])).

tff(c_1376,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1347])).

tff(c_969,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_1445,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_969])).

tff(c_1496,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1445,c_116])).

tff(c_1501,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1496])).

tff(c_1503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_1501])).

tff(c_1505,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1519,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1505,c_30])).

tff(c_1520,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1519])).

tff(c_1504,plain,(
    v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1551,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_1505,c_32])).

tff(c_1554,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1551,c_6])).

tff(c_1562,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1504,c_1554])).

tff(c_1573,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1562])).

tff(c_1579,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1573])).

tff(c_1585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1579])).

tff(c_1587,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1562])).

tff(c_1525,plain,(
    ! [C_168,A_169,D_170,B_171] :
      ( C_168 = A_169
      | g1_pre_topc(C_168,D_170) != g1_pre_topc(A_169,B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k1_zfmisc_1(A_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1527,plain,(
    ! [A_1,A_169,B_171] :
      ( u1_struct_0(A_1) = A_169
      | g1_pre_topc(A_169,B_171) != A_1
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k1_zfmisc_1(A_169)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1525])).

tff(c_1650,plain,(
    ! [A_199,B_200] :
      ( u1_struct_0(g1_pre_topc(A_199,B_200)) = A_199
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k1_zfmisc_1(A_199)))
      | ~ v1_pre_topc(g1_pre_topc(A_199,B_200))
      | ~ l1_pre_topc(g1_pre_topc(A_199,B_200)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1527])).

tff(c_1660,plain,(
    ! [A_203] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_203),u1_pre_topc(A_203))) = u1_struct_0(A_203)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_203),u1_pre_topc(A_203)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_203),u1_pre_topc(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(resolution,[status(thm)],[c_12,c_1650])).

tff(c_1668,plain,(
    ! [A_204] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_204),u1_pre_topc(A_204))) = u1_struct_0(A_204)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_204),u1_pre_topc(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(resolution,[status(thm)],[c_51,c_1660])).

tff(c_1671,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1587,c_1668])).

tff(c_1680,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1671])).

tff(c_1719,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_12])).

tff(c_1740,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1719])).

tff(c_1534,plain,(
    ! [D_172,B_173,C_174,A_175] :
      ( D_172 = B_173
      | g1_pre_topc(C_174,D_172) != g1_pre_topc(A_175,B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(A_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1538,plain,(
    ! [A_1,D_172,C_174] :
      ( u1_pre_topc(A_1) = D_172
      | g1_pre_topc(C_174,D_172) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1534])).

tff(c_1900,plain,(
    ! [C_209,D_210] :
      ( u1_pre_topc(g1_pre_topc(C_209,D_210)) = D_210
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_209,D_210)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_209,D_210)))))
      | ~ v1_pre_topc(g1_pre_topc(C_209,D_210))
      | ~ l1_pre_topc(g1_pre_topc(C_209,D_210)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1538])).

tff(c_1909,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_1900])).

tff(c_1922,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1740,c_1909])).

tff(c_1964,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1922])).

tff(c_1970,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_1964])).

tff(c_1976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1970])).

tff(c_1977,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1922])).

tff(c_1586,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_1562])).

tff(c_2003,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_1586])).

tff(c_1540,plain,(
    ! [B_179,A_180] :
      ( v3_pre_topc(B_179,A_180)
      | ~ r2_hidden(B_179,u1_pre_topc(A_180))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1544,plain,(
    ! [A_25,A_7] :
      ( v3_pre_topc(A_25,A_7)
      | ~ r2_hidden(A_25,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_59,c_1540])).

tff(c_2048,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2003,c_1544])).

tff(c_2053,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2048])).

tff(c_2055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1520,c_2053])).

tff(c_2056,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_2064,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_1505,c_32])).

tff(c_2110,plain,(
    ! [B_232,A_233] :
      ( r2_hidden(B_232,u1_pre_topc(A_233))
      | ~ v3_pre_topc(B_232,A_233)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2113,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2064,c_2110])).

tff(c_2119,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1504,c_2113])).

tff(c_2121,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2119])).

tff(c_2128,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2121])).

tff(c_2134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2128])).

tff(c_2136,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2119])).

tff(c_2093,plain,(
    ! [C_221,A_222,D_223,B_224] :
      ( C_221 = A_222
      | g1_pre_topc(C_221,D_223) != g1_pre_topc(A_222,B_224)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k1_zfmisc_1(A_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2095,plain,(
    ! [A_1,A_222,B_224] :
      ( u1_struct_0(A_1) = A_222
      | g1_pre_topc(A_222,B_224) != A_1
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k1_zfmisc_1(A_222)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2093])).

tff(c_2202,plain,(
    ! [A_247,B_248] :
      ( u1_struct_0(g1_pre_topc(A_247,B_248)) = A_247
      | ~ m1_subset_1(B_248,k1_zfmisc_1(k1_zfmisc_1(A_247)))
      | ~ v1_pre_topc(g1_pre_topc(A_247,B_248))
      | ~ l1_pre_topc(g1_pre_topc(A_247,B_248)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2095])).

tff(c_2212,plain,(
    ! [A_251] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251))) = u1_struct_0(A_251)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(resolution,[status(thm)],[c_12,c_2202])).

tff(c_2220,plain,(
    ! [A_252] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_252),u1_pre_topc(A_252))) = u1_struct_0(A_252)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_252),u1_pre_topc(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(resolution,[status(thm)],[c_51,c_2212])).

tff(c_2223,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2136,c_2220])).

tff(c_2232,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2223])).

tff(c_2235,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2232,c_2064])).

tff(c_2237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2056,c_2235])).

tff(c_2239,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2242,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2239,c_36])).

tff(c_2243,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2242])).

tff(c_2238,plain,(
    v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2274,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_2239,c_38])).

tff(c_2320,plain,(
    ! [B_277,A_278] :
      ( r2_hidden(B_277,u1_pre_topc(A_278))
      | ~ v3_pre_topc(B_277,A_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2323,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2274,c_2320])).

tff(c_2329,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2238,c_2323])).

tff(c_2331,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2329])).

tff(c_2337,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2331])).

tff(c_2343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2337])).

tff(c_2345,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2329])).

tff(c_2293,plain,(
    ! [C_262,A_263,D_264,B_265] :
      ( C_262 = A_263
      | g1_pre_topc(C_262,D_264) != g1_pre_topc(A_263,B_265)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(k1_zfmisc_1(A_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2295,plain,(
    ! [A_1,A_263,B_265] :
      ( u1_struct_0(A_1) = A_263
      | g1_pre_topc(A_263,B_265) != A_1
      | ~ m1_subset_1(B_265,k1_zfmisc_1(k1_zfmisc_1(A_263)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2293])).

tff(c_2408,plain,(
    ! [A_292,B_293] :
      ( u1_struct_0(g1_pre_topc(A_292,B_293)) = A_292
      | ~ m1_subset_1(B_293,k1_zfmisc_1(k1_zfmisc_1(A_292)))
      | ~ v1_pre_topc(g1_pre_topc(A_292,B_293))
      | ~ l1_pre_topc(g1_pre_topc(A_292,B_293)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2295])).

tff(c_2419,plain,(
    ! [A_296] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_296),u1_pre_topc(A_296))) = u1_struct_0(A_296)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_296),u1_pre_topc(A_296)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_296),u1_pre_topc(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_12,c_2408])).

tff(c_2427,plain,(
    ! [A_297] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_297),u1_pre_topc(A_297))) = u1_struct_0(A_297)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_297),u1_pre_topc(A_297)))
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_51,c_2419])).

tff(c_2430,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2345,c_2427])).

tff(c_2439,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2430])).

tff(c_2455,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_2])).

tff(c_2477,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_2455])).

tff(c_2736,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2477])).

tff(c_2742,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_2736])).

tff(c_2748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2742])).

tff(c_2750,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2477])).

tff(c_2302,plain,(
    ! [D_266,B_267,C_268,A_269] :
      ( D_266 = B_267
      | g1_pre_topc(C_268,D_266) != g1_pre_topc(A_269,B_267)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(k1_zfmisc_1(A_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2306,plain,(
    ! [A_1,D_266,C_268] :
      ( u1_pre_topc(A_1) = D_266
      | g1_pre_topc(C_268,D_266) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2302])).

tff(c_2497,plain,(
    ! [C_299,D_300] :
      ( u1_pre_topc(g1_pre_topc(C_299,D_300)) = D_300
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_299,D_300)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_299,D_300)))))
      | ~ v1_pre_topc(g1_pre_topc(C_299,D_300))
      | ~ l1_pre_topc(g1_pre_topc(C_299,D_300)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2306])).

tff(c_2512,plain,(
    ! [C_299,D_300] :
      ( u1_pre_topc(g1_pre_topc(C_299,D_300)) = D_300
      | ~ v1_pre_topc(g1_pre_topc(C_299,D_300))
      | ~ l1_pre_topc(g1_pre_topc(C_299,D_300)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2497])).

tff(c_2756,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2750,c_2512])).

tff(c_2765,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_2756])).

tff(c_2344,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2329])).

tff(c_2776,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2765,c_2344])).

tff(c_2265,plain,(
    ! [A_256,C_257,B_258] :
      ( m1_subset_1(A_256,C_257)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(C_257))
      | ~ r2_hidden(A_256,B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2268,plain,(
    ! [A_256,A_7] :
      ( m1_subset_1(A_256,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ r2_hidden(A_256,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_2265])).

tff(c_2308,plain,(
    ! [B_273,A_274] :
      ( v3_pre_topc(B_273,A_274)
      | ~ r2_hidden(B_273,u1_pre_topc(A_274))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2317,plain,(
    ! [A_256,A_7] :
      ( v3_pre_topc(A_256,A_7)
      | ~ r2_hidden(A_256,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_2268,c_2308])).

tff(c_2822,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2776,c_2317])).

tff(c_2827,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2822])).

tff(c_2829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2243,c_2827])).

tff(c_2830,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2242])).

tff(c_2867,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_2239,c_38])).

tff(c_2916,plain,(
    ! [B_331,A_332] :
      ( r2_hidden(B_331,u1_pre_topc(A_332))
      | ~ v3_pre_topc(B_331,A_332)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ l1_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2919,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2867,c_2916])).

tff(c_2925,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2238,c_2919])).

tff(c_2927,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2925])).

tff(c_2933,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2927])).

tff(c_2939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2933])).

tff(c_2941,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2925])).

tff(c_2887,plain,(
    ! [C_316,A_317,D_318,B_319] :
      ( C_316 = A_317
      | g1_pre_topc(C_316,D_318) != g1_pre_topc(A_317,B_319)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k1_zfmisc_1(A_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2889,plain,(
    ! [A_1,A_317,B_319] :
      ( u1_struct_0(A_1) = A_317
      | g1_pre_topc(A_317,B_319) != A_1
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k1_zfmisc_1(A_317)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2887])).

tff(c_3007,plain,(
    ! [A_346,B_347] :
      ( u1_struct_0(g1_pre_topc(A_346,B_347)) = A_346
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k1_zfmisc_1(A_346)))
      | ~ v1_pre_topc(g1_pre_topc(A_346,B_347))
      | ~ l1_pre_topc(g1_pre_topc(A_346,B_347)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2889])).

tff(c_3018,plain,(
    ! [A_350] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_350),u1_pre_topc(A_350))) = u1_struct_0(A_350)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_350),u1_pre_topc(A_350)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_350),u1_pre_topc(A_350)))
      | ~ l1_pre_topc(A_350) ) ),
    inference(resolution,[status(thm)],[c_12,c_3007])).

tff(c_3026,plain,(
    ! [A_351] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_351),u1_pre_topc(A_351))) = u1_struct_0(A_351)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_351),u1_pre_topc(A_351)))
      | ~ l1_pre_topc(A_351) ) ),
    inference(resolution,[status(thm)],[c_51,c_3018])).

tff(c_3029,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2941,c_3026])).

tff(c_3038,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3029])).

tff(c_3041,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_2867])).

tff(c_3043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2830,c_3041])).

%------------------------------------------------------------------------------
