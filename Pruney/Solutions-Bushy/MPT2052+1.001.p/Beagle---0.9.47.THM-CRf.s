%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2052+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:48 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 253 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 ( 884 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > l1_struct_0 > k2_yellow19 > a_2_1_yellow19 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(a_2_1_yellow19,type,(
    a_2_1_yellow19: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( r2_hidden(C,k2_yellow19(A,B))
              <=> ( r1_waybel_0(A,B,C)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => k2_yellow19(A,B) = a_2_1_yellow19(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_yellow19)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B) )
     => ( r2_hidden(A,a_2_1_yellow19(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & A = D
            & r1_waybel_0(B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow19)).

tff(c_14,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,
    ( r1_waybel_0('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r1_waybel_0('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_2','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_16,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( k2_yellow19(A_14,B_15) = a_2_1_yellow19(A_14,B_15)
      | ~ l1_waybel_0(B_15,A_14)
      | v2_struct_0(B_15)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_42,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_39])).

tff(c_43,plain,(
    k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_42])).

tff(c_30,plain,
    ( r1_waybel_0('#skF_2','#skF_3','#skF_4')
    | r2_hidden('#skF_5',k2_yellow19('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31,plain,(
    r2_hidden('#skF_5',k2_yellow19('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_44,plain,(
    r2_hidden('#skF_5',a_2_1_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_31])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( '#skF_1'(A_4,B_5,C_6) = A_4
      | ~ r2_hidden(A_4,a_2_1_yellow19(B_5,C_6))
      | ~ l1_waybel_0(C_6,B_5)
      | v2_struct_0(C_6)
      | ~ l1_struct_0(B_5)
      | v2_struct_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,
    ( '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_8])).

tff(c_55,plain,
    ( '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_52])).

tff(c_56,plain,(
    '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_55])).

tff(c_61,plain,(
    ! [B_19,C_20,A_21] :
      ( r1_waybel_0(B_19,C_20,'#skF_1'(A_21,B_19,C_20))
      | ~ r2_hidden(A_21,a_2_1_yellow19(B_19,C_20))
      | ~ l1_waybel_0(C_20,B_19)
      | v2_struct_0(C_20)
      | ~ l1_struct_0(B_19)
      | v2_struct_0(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,
    ( r1_waybel_0('#skF_2','#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5',a_2_1_yellow19('#skF_2','#skF_3'))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_61])).

tff(c_66,plain,
    ( r1_waybel_0('#skF_2','#skF_3','#skF_5')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_44,c_64])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_34,c_66])).

tff(c_69,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r1_waybel_0('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_77,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_80,plain,(
    ! [A_22,B_23] :
      ( k2_yellow19(A_22,B_23) = a_2_1_yellow19(A_22,B_23)
      | ~ l1_waybel_0(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_86,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_83])).

tff(c_87,plain,(
    k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_86])).

tff(c_88,plain,(
    r2_hidden('#skF_5',a_2_1_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_31])).

tff(c_93,plain,(
    ! [A_24,B_25,C_26] :
      ( '#skF_1'(A_24,B_25,C_26) = A_24
      | ~ r2_hidden(A_24,a_2_1_yellow19(B_25,C_26))
      | ~ l1_waybel_0(C_26,B_25)
      | v2_struct_0(C_26)
      | ~ l1_struct_0(B_25)
      | v2_struct_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,
    ( '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_93])).

tff(c_99,plain,
    ( '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_96])).

tff(c_100,plain,(
    '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_99])).

tff(c_112,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1('#skF_1'(A_30,B_31,C_32),k1_zfmisc_1(u1_struct_0(B_31)))
      | ~ r2_hidden(A_30,a_2_1_yellow19(B_31,C_32))
      | ~ l1_waybel_0(C_32,B_31)
      | v2_struct_0(C_32)
      | ~ l1_struct_0(B_31)
      | v2_struct_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_5',a_2_1_yellow19('#skF_2','#skF_3'))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_112])).

tff(c_117,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_88,c_115])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_77,c_117])).

tff(c_120,plain,(
    r1_waybel_0('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_70,plain,(
    r1_waybel_0('#skF_2','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_121,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_22,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r1_waybel_0('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_125,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_121,c_22])).

tff(c_166,plain,(
    ! [D_44,B_45,C_46] :
      ( r2_hidden(D_44,a_2_1_yellow19(B_45,C_46))
      | ~ r1_waybel_0(B_45,C_46,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(B_45)))
      | ~ l1_waybel_0(C_46,B_45)
      | v2_struct_0(C_46)
      | ~ l1_struct_0(B_45)
      | v2_struct_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,(
    ! [C_46] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_2',C_46))
      | ~ r1_waybel_0('#skF_2',C_46,'#skF_4')
      | ~ l1_waybel_0(C_46,'#skF_2')
      | v2_struct_0(C_46)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_125,c_166])).

tff(c_176,plain,(
    ! [C_46] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_2',C_46))
      | ~ r1_waybel_0('#skF_2',C_46,'#skF_4')
      | ~ l1_waybel_0(C_46,'#skF_2')
      | v2_struct_0(C_46)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_170])).

tff(c_182,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_2',C_47))
      | ~ r1_waybel_0('#skF_2',C_47,'#skF_4')
      | ~ l1_waybel_0(C_47,'#skF_2')
      | v2_struct_0(C_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_176])).

tff(c_126,plain,(
    ! [A_33,B_34] :
      ( k2_yellow19(A_33,B_34) = a_2_1_yellow19(A_33,B_34)
      | ~ l1_waybel_0(B_34,A_33)
      | v2_struct_0(B_34)
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_132,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_129])).

tff(c_133,plain,(
    k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_132])).

tff(c_20,plain,
    ( ~ r2_hidden('#skF_4',k2_yellow19('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r1_waybel_0('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_71,plain,(
    ~ r1_waybel_0('#skF_2','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_71])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_4',k2_yellow19('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_4',k2_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_74])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_123])).

tff(c_188,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_3','#skF_4')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_134])).

tff(c_195,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_120,c_188])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_195])).

tff(c_198,plain,(
    r1_waybel_0('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_199,plain,(
    ~ r2_hidden('#skF_5',k2_yellow19('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r2_hidden('#skF_5',k2_yellow19('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_200,plain,(
    r2_hidden('#skF_5',k2_yellow19('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_200])).

tff(c_202,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_224,plain,(
    ! [D_59,B_60,C_61] :
      ( r2_hidden(D_59,a_2_1_yellow19(B_60,C_61))
      | ~ r1_waybel_0(B_60,C_61,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(u1_struct_0(B_60)))
      | ~ l1_waybel_0(C_61,B_60)
      | v2_struct_0(C_61)
      | ~ l1_struct_0(B_60)
      | v2_struct_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_228,plain,(
    ! [C_61] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_2',C_61))
      | ~ r1_waybel_0('#skF_2',C_61,'#skF_4')
      | ~ l1_waybel_0(C_61,'#skF_2')
      | v2_struct_0(C_61)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_202,c_224])).

tff(c_232,plain,(
    ! [C_61] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_2',C_61))
      | ~ r1_waybel_0('#skF_2',C_61,'#skF_4')
      | ~ l1_waybel_0(C_61,'#skF_2')
      | v2_struct_0(C_61)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_234,plain,(
    ! [C_62] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_2',C_62))
      | ~ r1_waybel_0('#skF_2',C_62,'#skF_4')
      | ~ l1_waybel_0(C_62,'#skF_2')
      | v2_struct_0(C_62) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_232])).

tff(c_207,plain,(
    ! [A_48,B_49] :
      ( k2_yellow19(A_48,B_49) = a_2_1_yellow19(A_48,B_49)
      | ~ l1_waybel_0(B_49,A_48)
      | v2_struct_0(B_49)
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_210,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_207])).

tff(c_213,plain,
    ( k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_210])).

tff(c_214,plain,(
    k2_yellow19('#skF_2','#skF_3') = a_2_1_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_14,c_213])).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_4',k2_yellow19('#skF_2','#skF_3'))
    | r2_hidden('#skF_5',k2_yellow19('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_4',k2_yellow19('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_26])).

tff(c_215,plain,(
    ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_204])).

tff(c_240,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_3','#skF_4')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_215])).

tff(c_247,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_198,c_240])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_247])).

%------------------------------------------------------------------------------
