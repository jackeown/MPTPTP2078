%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1317+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:47 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 148 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 ( 449 expanded)
%              Number of equality atoms :    3 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v2_tops_2(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                     => ( D = B
                       => v2_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_2)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_18,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ~ v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_35,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_60,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),B_57)
      | v2_tops_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_29,c_60])).

tff(c_67,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_62])).

tff(c_68,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_67])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_45,C_46,B_47] :
      ( m1_subset_1(A_45,C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_112,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_pre_topc(C_68,A_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ v2_tops_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_134,plain,(
    ! [A_74] :
      ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),A_74)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ v2_tops_2('#skF_3',A_74)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_74))))
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_68,c_112])).

tff(c_142,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | ~ v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_153,plain,(
    v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28,c_26,c_22,c_142])).

tff(c_47,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_29,c_42])).

tff(c_84,plain,(
    ! [D_63,C_64,A_65] :
      ( v4_pre_topc(D_63,C_64)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0(C_64)))
      | ~ v4_pre_topc(D_63,A_65)
      | ~ m1_pre_topc(C_64,A_65)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    ! [A_71,A_72] :
      ( v4_pre_topc(A_71,'#skF_4')
      | ~ v4_pre_topc(A_71,A_72)
      | ~ m1_pre_topc('#skF_4',A_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ r2_hidden(A_71,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_47,c_84])).

tff(c_122,plain,(
    ! [A_45] :
      ( v4_pre_topc(A_45,'#skF_4')
      | ~ v4_pre_topc(A_45,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_116])).

tff(c_129,plain,(
    ! [A_45] :
      ( v4_pre_topc(A_45,'#skF_4')
      | ~ v4_pre_topc(A_45,'#skF_2')
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_122])).

tff(c_159,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_129])).

tff(c_162,plain,(
    v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_159])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v4_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,
    ( v2_tops_2('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_167,plain,(
    v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_167])).

%------------------------------------------------------------------------------
