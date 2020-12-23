%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1781+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:22 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  127 (1547 expanded)
%              Number of leaves         :   39 ( 590 expanded)
%              Depth                    :   26
%              Number of atoms          :  364 (10088 expanded)
%              Number of equality atoms :   27 ( 594 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k3_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_struct_0)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( r2_hidden(F,u1_struct_0(C))
                             => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k3_struct_0(A) = k6_partfun1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_struct_0)).

tff(f_75,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( k2_tmap_1(A_2,A_2,k3_struct_0(A_2),B_4) = k4_tmap_1(A_2,B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_5] :
      ( m1_subset_1(k3_struct_0(A_5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(A_5))))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_127,plain,(
    ! [B_115,C_114,A_116,E_117,D_113] :
      ( r2_hidden('#skF_1'(D_113,C_114,B_115,A_116,E_117),u1_struct_0(C_114))
      | r2_funct_2(u1_struct_0(C_114),u1_struct_0(A_116),k2_tmap_1(B_115,A_116,D_113,C_114),E_117)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_114),u1_struct_0(A_116))))
      | ~ v1_funct_2(E_117,u1_struct_0(C_114),u1_struct_0(A_116))
      | ~ v1_funct_1(E_117)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115),u1_struct_0(A_116))))
      | ~ v1_funct_2(D_113,u1_struct_0(B_115),u1_struct_0(A_116))
      | ~ v1_funct_1(D_113)
      | ~ m1_pre_topc(C_114,B_115)
      | v2_struct_0(C_114)
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_131,plain,(
    ! [D_113,B_115] :
      ( r2_hidden('#skF_1'(D_113,'#skF_3',B_115,'#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_115,'#skF_2',D_113,'#skF_3'),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_113,u1_struct_0(B_115),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_113)
      | ~ m1_pre_topc('#skF_3',B_115)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_135,plain,(
    ! [D_113,B_115] :
      ( r2_hidden('#skF_1'(D_113,'#skF_3',B_115,'#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_115,'#skF_2',D_113,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_113,u1_struct_0(B_115),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_113)
      | ~ m1_pre_topc('#skF_3',B_115)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_36,c_131])).

tff(c_137,plain,(
    ! [D_118,B_119] :
      ( r2_hidden('#skF_1'(D_118,'#skF_3',B_119,'#skF_2','#skF_4'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_119,'#skF_2',D_118,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_119),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_118,u1_struct_0(B_119),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_118)
      | ~ m1_pre_topc('#skF_3',B_119)
      | ~ l1_pre_topc(B_119)
      | ~ v2_pre_topc(B_119)
      | v2_struct_0(B_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_135])).

tff(c_141,plain,
    ( r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_147,plain,
    ( r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_141])).

tff(c_148,plain,
    ( r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_147])).

tff(c_153,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_156,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_153])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_156])).

tff(c_162,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_funct_1(k3_struct_0(A_5))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_funct_2(k3_struct_0(A_5),u1_struct_0(A_5),u1_struct_0(A_5))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_161,plain,
    ( ~ v1_funct_1(k3_struct_0('#skF_2'))
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_163,plain,(
    ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_176])).

tff(c_181,plain,
    ( ~ v1_funct_1(k3_struct_0('#skF_2'))
    | r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_183,plain,(
    ~ v1_funct_1(k3_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_186,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_186])).

tff(c_192,plain,(
    v1_funct_1(k3_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_182,plain,(
    v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_191,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_193,plain,(
    r2_hidden('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_32,plain,(
    ! [D_90] :
      ( k1_funct_1('#skF_4',D_90) = D_90
      | ~ r2_hidden(D_90,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_90,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_200,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_193,c_32])).

tff(c_202,plain,(
    ~ m1_subset_1('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_203,plain,(
    ! [C_126,A_128,D_125,E_129,B_127] :
      ( m1_subset_1('#skF_1'(D_125,C_126,B_127,A_128,E_129),u1_struct_0(B_127))
      | r2_funct_2(u1_struct_0(C_126),u1_struct_0(A_128),k2_tmap_1(B_127,A_128,D_125,C_126),E_129)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_126),u1_struct_0(A_128))))
      | ~ v1_funct_2(E_129,u1_struct_0(C_126),u1_struct_0(A_128))
      | ~ v1_funct_1(E_129)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_127),u1_struct_0(A_128))))
      | ~ v1_funct_2(D_125,u1_struct_0(B_127),u1_struct_0(A_128))
      | ~ v1_funct_1(D_125)
      | ~ m1_pre_topc(C_126,B_127)
      | v2_struct_0(C_126)
      | ~ l1_pre_topc(B_127)
      | ~ v2_pre_topc(B_127)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_207,plain,(
    ! [D_125,B_127] :
      ( m1_subset_1('#skF_1'(D_125,'#skF_3',B_127,'#skF_2','#skF_4'),u1_struct_0(B_127))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_127,'#skF_2',D_125,'#skF_3'),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_127),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_125,u1_struct_0(B_127),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_125)
      | ~ m1_pre_topc('#skF_3',B_127)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_127)
      | ~ v2_pre_topc(B_127)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_203])).

tff(c_211,plain,(
    ! [D_125,B_127] :
      ( m1_subset_1('#skF_1'(D_125,'#skF_3',B_127,'#skF_2','#skF_4'),u1_struct_0(B_127))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_127,'#skF_2',D_125,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_127),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_125,u1_struct_0(B_127),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_125)
      | ~ m1_pre_topc('#skF_3',B_127)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_127)
      | ~ v2_pre_topc(B_127)
      | v2_struct_0(B_127)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_36,c_207])).

tff(c_213,plain,(
    ! [D_130,B_131] :
      ( m1_subset_1('#skF_1'(D_130,'#skF_3',B_131,'#skF_2','#skF_4'),u1_struct_0(B_131))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_131,'#skF_2',D_130,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_131),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_130,u1_struct_0(B_131),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_130)
      | ~ m1_pre_topc('#skF_3',B_131)
      | ~ l1_pre_topc(B_131)
      | ~ v2_pre_topc(B_131)
      | v2_struct_0(B_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_211])).

tff(c_216,plain,
    ( m1_subset_1('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_213])).

tff(c_221,plain,
    ( m1_subset_1('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_46,c_44,c_40,c_192,c_182,c_216])).

tff(c_222,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_202,c_221])).

tff(c_229,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_222])).

tff(c_231,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_229])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_30,c_231])).

tff(c_234,plain,(
    k1_funct_1('#skF_4','#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_235,plain,(
    m1_subset_1('#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] :
      ( k6_partfun1(u1_struct_0(A_1)) = k3_struct_0(A_1)
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18,plain,(
    ! [A_12] : k6_relat_1(A_12) = k6_partfun1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k1_funct_1(k6_relat_1(B_16),A_15) = A_15
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_71,plain,(
    ! [B_96,A_97] :
      ( k1_funct_1(k6_partfun1(B_96),A_97) = A_97
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_86,plain,(
    ! [A_102,A_103] :
      ( k1_funct_1(k3_struct_0(A_102),A_103) = A_103
      | ~ r2_hidden(A_103,u1_struct_0(A_102))
      | ~ l1_struct_0(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_71])).

tff(c_91,plain,(
    ! [A_102,A_13] :
      ( k1_funct_1(k3_struct_0(A_102),A_13) = A_13
      | ~ l1_struct_0(A_102)
      | v1_xboole_0(u1_struct_0(A_102))
      | ~ m1_subset_1(A_13,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_240,plain,
    ( k1_funct_1(k3_struct_0('#skF_2'),'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_235,c_91])).

tff(c_244,plain,
    ( k1_funct_1(k3_struct_0('#skF_2'),'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_240])).

tff(c_249,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_252,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_14])).

tff(c_255,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_255])).

tff(c_258,plain,(
    k1_funct_1(k3_struct_0('#skF_2'),'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_259,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k3_funct_2(A_8,B_9,C_10,D_11) = k1_funct_1(C_10,D_11)
      | ~ m1_subset_1(D_11,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_241,plain,(
    ! [B_9,C_10] :
      ( k3_funct_2(u1_struct_0('#skF_2'),B_9,C_10,'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = k1_funct_1(C_10,'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),B_9)))
      | ~ v1_funct_2(C_10,u1_struct_0('#skF_2'),B_9)
      | ~ v1_funct_1(C_10)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_235,c_16])).

tff(c_265,plain,(
    ! [B_132,C_133] :
      ( k3_funct_2(u1_struct_0('#skF_2'),B_132,C_133,'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = k1_funct_1(C_133,'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),B_132)))
      | ~ v1_funct_2(C_133,u1_struct_0('#skF_2'),B_132)
      | ~ v1_funct_1(C_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_241])).

tff(c_269,plain,
    ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k3_struct_0('#skF_2'),'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = k1_funct_1(k3_struct_0('#skF_2'),'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4'))
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_265])).

tff(c_272,plain,(
    k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k3_struct_0('#skF_2'),'#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) = '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_192,c_182,c_258,c_269])).

tff(c_302,plain,(
    ! [D_144,E_148,C_145,B_146,A_147] :
      ( k3_funct_2(u1_struct_0(B_146),u1_struct_0(A_147),D_144,'#skF_1'(D_144,C_145,B_146,A_147,E_148)) != k1_funct_1(E_148,'#skF_1'(D_144,C_145,B_146,A_147,E_148))
      | r2_funct_2(u1_struct_0(C_145),u1_struct_0(A_147),k2_tmap_1(B_146,A_147,D_144,C_145),E_148)
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145),u1_struct_0(A_147))))
      | ~ v1_funct_2(E_148,u1_struct_0(C_145),u1_struct_0(A_147))
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_146),u1_struct_0(A_147))))
      | ~ v1_funct_2(D_144,u1_struct_0(B_146),u1_struct_0(A_147))
      | ~ v1_funct_1(D_144)
      | ~ m1_pre_topc(C_145,B_146)
      | v2_struct_0(C_145)
      | ~ l1_pre_topc(B_146)
      | ~ v2_pre_topc(B_146)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_304,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')) != '#skF_1'(k3_struct_0('#skF_2'),'#skF_3','#skF_2','#skF_2','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k3_struct_0('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_302])).

tff(c_309,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ m1_subset_1(k3_struct_0('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_46,c_44,c_40,c_192,c_182,c_38,c_36,c_34,c_234,c_304])).

tff(c_310,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | ~ m1_subset_1(k3_struct_0('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_309])).

tff(c_311,plain,(
    ~ m1_subset_1(k3_struct_0('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_314,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_314])).

tff(c_319,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_357,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_319])).

tff(c_359,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_357])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_30,c_359])).

tff(c_362,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_2','#skF_2',k3_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_381,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_362])).

tff(c_383,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_381])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_30,c_383])).

%------------------------------------------------------------------------------
