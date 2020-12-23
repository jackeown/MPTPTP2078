%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:48 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 574 expanded)
%              Number of leaves         :   32 ( 223 expanded)
%              Depth                    :   22
%              Number of atoms          :  322 (3388 expanded)
%              Number of equality atoms :   25 ( 257 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_18,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k4_tmap_1(A_27,B_28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_28),u1_struct_0(A_27))))
      | ~ m1_pre_topc(B_28,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( v1_funct_1(k4_tmap_1(A_27,B_28))
      | ~ m1_pre_topc(B_28,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_87,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( m1_subset_1('#skF_1'(A_68,B_69,C_70,D_71),A_68)
      | r2_funct_2(A_68,B_69,C_70,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(D_71,A_68,B_69)
      | ~ v1_funct_1(D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(C_70,A_68,B_69)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [C_70] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_70,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_30,c_87])).

tff(c_95,plain,(
    ! [C_70] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_70,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_91])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_97,plain,(
    ! [C_75] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_75,'#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_75,'#skF_4')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_91])).

tff(c_16,plain,(
    ! [C_26,A_20,B_24] :
      ( m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(C_26,u1_struct_0(B_24))
      | ~ m1_pre_topc(B_24,A_20)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_101,plain,(
    ! [C_75,A_20] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_75,'#skF_4'),u1_struct_0(A_20))
      | ~ m1_pre_topc('#skF_3',A_20)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_75,'#skF_4')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_119,plain,(
    ! [C_81,A_82] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4'),u1_struct_0(A_82))
      | ~ m1_pre_topc('#skF_3',A_82)
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_81,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_101])).

tff(c_46,plain,(
    ! [B_49,A_50] :
      ( l1_pre_topc(B_49)
      | ~ m1_pre_topc(B_49,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_49])).

tff(c_10,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_4',D_54) = D_54
      | ~ r2_hidden(D_54,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_54,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_62,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_14,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_14])).

tff(c_68,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_65])).

tff(c_71,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71])).

tff(c_76,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_129,plain,(
    ! [C_81] :
      ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4'),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_81,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_119,c_76])).

tff(c_135,plain,(
    ! [C_81] :
      ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4'),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2')
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_81,'#skF_4')
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_81,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_129])).

tff(c_178,plain,(
    ! [C_100] :
      ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_100,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_100,'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_100,'#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_100,'#skF_4')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_100,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_135])).

tff(c_191,plain,(
    ! [C_101] :
      ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_101,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_101,'#skF_4')
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_101,'#skF_4')
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_101,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_95,c_178])).

tff(c_195,plain,
    ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_191])).

tff(c_201,plain,
    ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_195])).

tff(c_202,plain,
    ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_26,c_201])).

tff(c_206,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_209,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_206])).

tff(c_212,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_209])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_212])).

tff(c_216,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_20,plain,(
    ! [A_27,B_28] :
      ( v1_funct_2(k4_tmap_1(A_27,B_28),u1_struct_0(B_28),u1_struct_0(A_27))
      | ~ m1_pre_topc(B_28,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_215,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_217,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_221,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_224,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_221])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_224])).

tff(c_228,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_227,plain,(
    k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_77,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_82,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_funct_1(k4_tmap_1(A_65,B_66),C_67) = C_67
      | ~ r2_hidden(C_67,u1_struct_0(B_66))
      | ~ m1_subset_1(C_67,u1_struct_0(A_65))
      | ~ m1_pre_topc(B_66,A_65)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_86,plain,(
    ! [A_65,B_66,A_1] :
      ( k1_funct_1(k4_tmap_1(A_65,B_66),A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0(A_65))
      | ~ m1_pre_topc(B_66,A_65)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | v1_xboole_0(u1_struct_0(B_66))
      | ~ m1_subset_1(A_1,u1_struct_0(B_66)) ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_253,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_funct_1(k4_tmap_1(A_112,B_113),'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_114,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_114,'#skF_4')
      | ~ m1_pre_topc(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ v2_pre_topc(A_112)
      | v1_xboole_0(u1_struct_0(B_113))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_114,'#skF_4'),u1_struct_0(B_113))
      | ~ m1_pre_topc('#skF_3',A_112)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_114,'#skF_4')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_114,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_119,c_86])).

tff(c_257,plain,(
    ! [A_112,C_70] :
      ( k1_funct_1(k4_tmap_1(A_112,'#skF_3'),'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc(A_112)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_112)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_70,'#skF_4')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_70,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_95,c_253])).

tff(c_262,plain,(
    ! [A_115,C_116] :
      ( k1_funct_1(k4_tmap_1(A_115,'#skF_3'),'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_116,'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_116,'#skF_4')
      | ~ v2_pre_topc(A_115)
      | ~ m1_pre_topc('#skF_3',A_115)
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),C_116,'#skF_4')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_116,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_38,c_257])).

tff(c_265,plain,(
    ! [A_115] :
      ( k1_funct_1(k4_tmap_1(A_115,'#skF_3'),'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ v2_pre_topc(A_115)
      | ~ m1_pre_topc('#skF_3',A_115)
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_262])).

tff(c_270,plain,(
    ! [A_115] :
      ( k1_funct_1(k4_tmap_1(A_115,'#skF_3'),'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ v2_pre_topc(A_115)
      | ~ m1_pre_topc('#skF_3',A_115)
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115)
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_216,c_228,c_265])).

tff(c_276,plain,(
    ! [A_122] :
      ( k1_funct_1(k4_tmap_1(A_122,'#skF_3'),'#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ v2_pre_topc(A_122)
      | ~ m1_pre_topc('#skF_3',A_122)
      | ~ l1_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_26,c_270])).

tff(c_6,plain,(
    ! [D_11,A_3,B_4,C_5] :
      ( k1_funct_1(D_11,'#skF_1'(A_3,B_4,C_5,D_11)) != k1_funct_1(C_5,'#skF_1'(A_3,B_4,C_5,D_11))
      | r2_funct_2(A_3,B_4,C_5,D_11)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(D_11,A_3,B_4)
      | ~ v1_funct_1(D_11)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(C_5,A_3,B_4)
      | ~ v1_funct_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_282,plain,
    ( k1_funct_1('#skF_4','#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_6])).

tff(c_288,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_42,c_216,c_228,c_34,c_32,c_30,c_227,c_282])).

tff(c_289,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_26,c_288])).

tff(c_293,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_289])).

tff(c_296,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_293])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.38  
% 2.64/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.38  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.64/1.38  
% 2.64/1.38  %Foreground sorts:
% 2.64/1.38  
% 2.64/1.38  
% 2.64/1.38  %Background operators:
% 2.64/1.38  
% 2.64/1.38  
% 2.64/1.38  %Foreground operators:
% 2.64/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.38  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 2.64/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.64/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.64/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.64/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.38  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.64/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.38  
% 2.92/1.41  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 2.92/1.41  tff(f_101, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 2.92/1.41  tff(f_51, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 2.92/1.41  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 2.92/1.41  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.92/1.41  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.92/1.41  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.92/1.41  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.92/1.41  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 2.92/1.41  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_18, plain, (![A_27, B_28]: (m1_subset_1(k4_tmap_1(A_27, B_28), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_28), u1_struct_0(A_27)))) | ~m1_pre_topc(B_28, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.92/1.41  tff(c_26, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_22, plain, (![A_27, B_28]: (v1_funct_1(k4_tmap_1(A_27, B_28)) | ~m1_pre_topc(B_28, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.92/1.41  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_87, plain, (![A_68, B_69, C_70, D_71]: (m1_subset_1('#skF_1'(A_68, B_69, C_70, D_71), A_68) | r2_funct_2(A_68, B_69, C_70, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(D_71, A_68, B_69) | ~v1_funct_1(D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(C_70, A_68, B_69) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.41  tff(c_91, plain, (![C_70]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_70, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_70))), inference(resolution, [status(thm)], [c_30, c_87])).
% 2.92/1.41  tff(c_95, plain, (![C_70]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_70, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_70))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_91])).
% 2.92/1.41  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_97, plain, (![C_75]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_75, '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_75, '#skF_4') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_75, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_75))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_91])).
% 2.92/1.41  tff(c_16, plain, (![C_26, A_20, B_24]: (m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(C_26, u1_struct_0(B_24)) | ~m1_pre_topc(B_24, A_20) | v2_struct_0(B_24) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.92/1.41  tff(c_101, plain, (![C_75, A_20]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_75, '#skF_4'), u1_struct_0(A_20)) | ~m1_pre_topc('#skF_3', A_20) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_20) | v2_struct_0(A_20) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_75, '#skF_4') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_75, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_75))), inference(resolution, [status(thm)], [c_97, c_16])).
% 2.92/1.41  tff(c_119, plain, (![C_81, A_82]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4'), u1_struct_0(A_82)) | ~m1_pre_topc('#skF_3', A_82) | ~l1_pre_topc(A_82) | v2_struct_0(A_82) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4') | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_81, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_81))), inference(negUnitSimplification, [status(thm)], [c_38, c_101])).
% 2.92/1.41  tff(c_46, plain, (![B_49, A_50]: (l1_pre_topc(B_49) | ~m1_pre_topc(B_49, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.41  tff(c_49, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_46])).
% 2.92/1.41  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_49])).
% 2.92/1.41  tff(c_10, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.41  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.41  tff(c_55, plain, (![D_54]: (k1_funct_1('#skF_4', D_54)=D_54 | ~r2_hidden(D_54, u1_struct_0('#skF_3')) | ~m1_subset_1(D_54, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.92/1.41  tff(c_60, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_55])).
% 2.92/1.41  tff(c_62, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 2.92/1.41  tff(c_14, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.92/1.41  tff(c_65, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_14])).
% 2.92/1.41  tff(c_68, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_65])).
% 2.92/1.41  tff(c_71, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_68])).
% 2.92/1.41  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_71])).
% 2.92/1.41  tff(c_76, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_60])).
% 2.92/1.41  tff(c_129, plain, (![C_81]: (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4') | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_81, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_81))), inference(resolution, [status(thm)], [c_119, c_76])).
% 2.92/1.41  tff(c_135, plain, (![C_81]: (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_2') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_81, '#skF_4') | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_81, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_81))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_129])).
% 2.92/1.41  tff(c_178, plain, (![C_100]: (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_100, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_100, '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_100, '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_100, '#skF_4') | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_100, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_100))), inference(negUnitSimplification, [status(thm)], [c_44, c_135])).
% 2.92/1.41  tff(c_191, plain, (![C_101]: (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_101, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_101, '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_101, '#skF_4') | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_101, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_101))), inference(resolution, [status(thm)], [c_95, c_178])).
% 2.92/1.41  tff(c_195, plain, (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_191])).
% 2.92/1.41  tff(c_201, plain, (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_195])).
% 2.92/1.41  tff(c_202, plain, (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_26, c_201])).
% 2.92/1.41  tff(c_206, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_202])).
% 2.92/1.41  tff(c_209, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_206])).
% 2.92/1.41  tff(c_212, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_209])).
% 2.92/1.41  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_212])).
% 2.92/1.41  tff(c_216, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_202])).
% 2.92/1.41  tff(c_20, plain, (![A_27, B_28]: (v1_funct_2(k4_tmap_1(A_27, B_28), u1_struct_0(B_28), u1_struct_0(A_27)) | ~m1_pre_topc(B_28, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.92/1.41  tff(c_215, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_202])).
% 2.92/1.41  tff(c_217, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_215])).
% 2.92/1.41  tff(c_221, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_217])).
% 2.92/1.41  tff(c_224, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_221])).
% 2.92/1.41  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_224])).
% 2.92/1.41  tff(c_228, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_215])).
% 2.92/1.41  tff(c_227, plain, (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_215])).
% 2.92/1.41  tff(c_77, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 2.92/1.41  tff(c_82, plain, (![A_65, B_66, C_67]: (k1_funct_1(k4_tmap_1(A_65, B_66), C_67)=C_67 | ~r2_hidden(C_67, u1_struct_0(B_66)) | ~m1_subset_1(C_67, u1_struct_0(A_65)) | ~m1_pre_topc(B_66, A_65) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.92/1.41  tff(c_86, plain, (![A_65, B_66, A_1]: (k1_funct_1(k4_tmap_1(A_65, B_66), A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0(A_65)) | ~m1_pre_topc(B_66, A_65) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | v1_xboole_0(u1_struct_0(B_66)) | ~m1_subset_1(A_1, u1_struct_0(B_66)))), inference(resolution, [status(thm)], [c_2, c_82])).
% 2.92/1.41  tff(c_253, plain, (![A_112, B_113, C_114]: (k1_funct_1(k4_tmap_1(A_112, B_113), '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_114, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_114, '#skF_4') | ~m1_pre_topc(B_113, A_112) | v2_struct_0(B_113) | ~v2_pre_topc(A_112) | v1_xboole_0(u1_struct_0(B_113)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_114, '#skF_4'), u1_struct_0(B_113)) | ~m1_pre_topc('#skF_3', A_112) | ~l1_pre_topc(A_112) | v2_struct_0(A_112) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_114, '#skF_4') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_114, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_114))), inference(resolution, [status(thm)], [c_119, c_86])).
% 2.92/1.41  tff(c_257, plain, (![A_112, C_70]: (k1_funct_1(k4_tmap_1(A_112, '#skF_3'), '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4') | v2_struct_0('#skF_3') | ~v2_pre_topc(A_112) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_112) | ~l1_pre_topc(A_112) | v2_struct_0(A_112) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_70, '#skF_4') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_70, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_70))), inference(resolution, [status(thm)], [c_95, c_253])).
% 2.92/1.41  tff(c_262, plain, (![A_115, C_116]: (k1_funct_1(k4_tmap_1(A_115, '#skF_3'), '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_116, '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_116, '#skF_4') | ~v2_pre_topc(A_115) | ~m1_pre_topc('#skF_3', A_115) | ~l1_pre_topc(A_115) | v2_struct_0(A_115) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), C_116, '#skF_4') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_116, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_116))), inference(negUnitSimplification, [status(thm)], [c_77, c_38, c_257])).
% 2.92/1.41  tff(c_265, plain, (![A_115]: (k1_funct_1(k4_tmap_1(A_115, '#skF_3'), '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v2_pre_topc(A_115) | ~m1_pre_topc('#skF_3', A_115) | ~l1_pre_topc(A_115) | v2_struct_0(A_115) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_262])).
% 2.92/1.41  tff(c_270, plain, (![A_115]: (k1_funct_1(k4_tmap_1(A_115, '#skF_3'), '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v2_pre_topc(A_115) | ~m1_pre_topc('#skF_3', A_115) | ~l1_pre_topc(A_115) | v2_struct_0(A_115) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_216, c_228, c_265])).
% 2.92/1.41  tff(c_276, plain, (![A_122]: (k1_funct_1(k4_tmap_1(A_122, '#skF_3'), '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~v2_pre_topc(A_122) | ~m1_pre_topc('#skF_3', A_122) | ~l1_pre_topc(A_122) | v2_struct_0(A_122))), inference(negUnitSimplification, [status(thm)], [c_44, c_26, c_270])).
% 2.92/1.41  tff(c_6, plain, (![D_11, A_3, B_4, C_5]: (k1_funct_1(D_11, '#skF_1'(A_3, B_4, C_5, D_11))!=k1_funct_1(C_5, '#skF_1'(A_3, B_4, C_5, D_11)) | r2_funct_2(A_3, B_4, C_5, D_11) | ~m1_subset_1(D_11, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(D_11, A_3, B_4) | ~v1_funct_1(D_11) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(C_5, A_3, B_4) | ~v1_funct_1(C_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.41  tff(c_282, plain, (k1_funct_1('#skF_4', '#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_276, c_6])).
% 2.92/1.41  tff(c_288, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_42, c_216, c_228, c_34, c_32, c_30, c_227, c_282])).
% 2.92/1.41  tff(c_289, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_26, c_288])).
% 2.92/1.41  tff(c_293, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_289])).
% 2.92/1.41  tff(c_296, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_293])).
% 2.92/1.41  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_296])).
% 2.92/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  Inference rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Ref     : 1
% 2.92/1.41  #Sup     : 44
% 2.92/1.41  #Fact    : 0
% 2.92/1.41  #Define  : 0
% 2.92/1.41  #Split   : 5
% 2.92/1.41  #Chain   : 0
% 2.92/1.41  #Close   : 0
% 2.92/1.41  
% 2.92/1.41  Ordering : KBO
% 2.92/1.41  
% 2.92/1.41  Simplification rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Subsume      : 3
% 2.92/1.41  #Demod        : 46
% 2.92/1.41  #Tautology    : 6
% 2.92/1.41  #SimpNegUnit  : 14
% 2.92/1.41  #BackRed      : 0
% 2.92/1.41  
% 2.92/1.41  #Partial instantiations: 0
% 2.92/1.41  #Strategies tried      : 1
% 2.92/1.41  
% 2.92/1.41  Timing (in seconds)
% 2.92/1.41  ----------------------
% 2.92/1.41  Preprocessing        : 0.31
% 2.92/1.41  Parsing              : 0.17
% 2.92/1.41  CNF conversion       : 0.02
% 2.92/1.41  Main loop            : 0.32
% 2.92/1.41  Inferencing          : 0.12
% 2.92/1.41  Reduction            : 0.08
% 2.92/1.41  Demodulation         : 0.06
% 2.92/1.41  BG Simplification    : 0.02
% 2.92/1.41  Subsumption          : 0.07
% 2.92/1.41  Abstraction          : 0.02
% 2.92/1.41  MUC search           : 0.00
% 2.92/1.41  Cooper               : 0.00
% 2.92/1.41  Total                : 0.68
% 2.92/1.41  Index Insertion      : 0.00
% 2.92/1.41  Index Deletion       : 0.00
% 2.92/1.41  Index Matching       : 0.00
% 2.92/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
