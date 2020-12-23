%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1316+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:47 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 137 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 451 expanded)
%              Number of equality atoms :    3 (  39 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v1_tops_2(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                     => ( D = B
                       => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_18,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    ~ v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_35,plain,(
    ! [B_47,A_48] :
      ( l1_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_41,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_22,plain,(
    v1_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1('#skF_1'(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | v1_tops_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [C_35,A_29,B_33] :
      ( m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(B_33)))
      | ~ m1_pre_topc(B_33,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_59,plain,(
    ! [A_56,B_57,A_29] :
      ( m1_subset_1('#skF_1'(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(A_56,A_29)
      | ~ l1_pre_topc(A_29)
      | v1_tops_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_56,c_14])).

tff(c_43,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),B_53)
      | v1_tops_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_52))))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_29,c_43])).

tff(c_50,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_45])).

tff(c_51,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_50])).

tff(c_64,plain,(
    ! [C_61,A_62,B_63] :
      ( v3_pre_topc(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ v1_tops_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_67] :
      ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),A_67)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v1_tops_2('#skF_3',A_67)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_51,c_64])).

tff(c_79,plain,(
    ! [A_29] :
      ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),A_29)
      | ~ v1_tops_2('#skF_3',A_29)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ m1_pre_topc('#skF_4',A_29)
      | ~ l1_pre_topc(A_29)
      | v1_tops_2('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_59,c_75])).

tff(c_86,plain,(
    ! [A_29] :
      ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),A_29)
      | ~ v1_tops_2('#skF_3',A_29)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ m1_pre_topc('#skF_4',A_29)
      | ~ l1_pre_topc(A_29)
      | v1_tops_2('#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_79])).

tff(c_92,plain,(
    ! [A_68] :
      ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),A_68)
      | ~ v1_tops_2('#skF_3',A_68)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | ~ m1_pre_topc('#skF_4',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_86])).

tff(c_98,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_tops_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_104,plain,(
    v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_98])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),k1_zfmisc_1(u1_struct_0(A_1)))
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [D_58,C_59,A_60] :
      ( v3_pre_topc(D_58,C_59)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(C_59)))
      | ~ v3_pre_topc(D_58,A_60)
      | ~ m1_pre_topc(C_59,A_60)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_142,plain,(
    ! [A_78,B_79,A_80] :
      ( v3_pre_topc('#skF_1'(A_78,B_79),A_78)
      | ~ v3_pre_topc('#skF_1'(A_78,B_79),A_80)
      | ~ m1_pre_topc(A_78,A_80)
      | ~ m1_subset_1('#skF_1'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | v1_tops_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_157,plain,(
    ! [A_81,B_82,A_83] :
      ( v3_pre_topc('#skF_1'(A_81,B_82),A_81)
      | ~ v3_pre_topc('#skF_1'(A_81,B_82),A_83)
      | ~ m1_pre_topc(A_81,A_83)
      | ~ l1_pre_topc(A_83)
      | v1_tops_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81))))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_59,c_142])).

tff(c_159,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v1_tops_2('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_157])).

tff(c_162,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_28,c_24,c_159])).

tff(c_163,plain,(
    v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_162])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,
    ( v1_tops_2('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_174,plain,(
    v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_167])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_174])).

%------------------------------------------------------------------------------
