%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 721 expanded)
%              Number of leaves         :   35 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  371 (6136 expanded)
%              Number of equality atoms :   44 ( 487 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_28,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    ! [A_155,B_156,D_157] :
      ( r2_funct_2(A_155,B_156,D_157,D_157)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(D_157,A_155,B_156)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_79,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_74])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_12,plain,(
    ! [A_67] :
      ( l1_struct_0(A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_119,plain,(
    ! [D_167,A_169,C_168,E_171,B_170] :
      ( r2_hidden('#skF_1'(D_167,C_168,A_169,B_170,E_171),D_167)
      | k2_partfun1(A_169,B_170,C_168,D_167) = E_171
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(D_167,B_170)))
      | ~ v1_funct_2(E_171,D_167,B_170)
      | ~ v1_funct_1(E_171)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_169))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_2(C_168,A_169,B_170)
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(B_170)
      | v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_121,plain,(
    ! [C_168,A_169] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_169))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_126,plain,(
    ! [C_168,A_169] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_169))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_121])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_16,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(u1_struct_0(A_71))
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_133,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_16])).

tff(c_136,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_133])).

tff(c_139,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_139])).

tff(c_145,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_123,plain,(
    ! [C_168,A_169] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_3'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_169))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_129,plain,(
    ! [C_168,A_169] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_3'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_169))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_123])).

tff(c_175,plain,(
    ! [C_168,A_169] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_3'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_3')) = '#skF_5'
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(A_169))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(A_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_129])).

tff(c_176,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_179,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_16])).

tff(c_182,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_179])).

tff(c_185,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_185])).

tff(c_191,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_20,plain,(
    ! [B_89,A_87] :
      ( m1_subset_1(u1_struct_0(B_89),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_pre_topc(B_89,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_55,plain,(
    ! [B_150,A_151] :
      ( l1_pre_topc(B_150)
      | ~ m1_pre_topc(B_150,A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_61,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_58])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_144,plain,(
    ! [C_168,A_169] :
      ( v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_169))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(A_169) ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_146,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_162,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_16])).

tff(c_165,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_162])).

tff(c_168,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_168])).

tff(c_174,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_173,plain,(
    ! [C_168,A_169] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),C_168,A_169,u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_169,u1_struct_0('#skF_2'),C_168,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_169))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_168,A_169,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(A_169) ) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_24,plain,(
    ! [F_147] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',F_147) = k1_funct_1('#skF_6',F_147)
      | ~ r2_hidden(F_147,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_147,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_241,plain,(
    ! [A_192,E_194,D_190,C_191,B_193] :
      ( k3_funct_2(A_192,B_193,C_191,'#skF_1'(D_190,C_191,A_192,B_193,E_194)) != k1_funct_1(E_194,'#skF_1'(D_190,C_191,A_192,B_193,E_194))
      | k2_partfun1(A_192,B_193,C_191,D_190) = E_194
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(D_190,B_193)))
      | ~ v1_funct_2(E_194,D_190,B_193)
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(A_192))
      | v1_xboole_0(D_190)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(C_191,A_192,B_193)
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(B_193)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_244,plain,(
    ! [E_194,D_190] :
      ( k1_funct_1(E_194,'#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194)) != k1_funct_1('#skF_6','#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_190) = E_194
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(D_190,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_194,D_190,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_190)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194),u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_241])).

tff(c_246,plain,(
    ! [E_194,D_190] :
      ( k1_funct_1(E_194,'#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194)) != k1_funct_1('#skF_6','#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_190) = E_194
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(D_190,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_194,D_190,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_190)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_244])).

tff(c_247,plain,(
    ! [E_194,D_190] :
      ( k1_funct_1(E_194,'#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194)) != k1_funct_1('#skF_6','#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_190) = E_194
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(D_190,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_194,D_190,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_190)
      | ~ r2_hidden('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),E_194),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_145,c_246])).

tff(c_250,plain,(
    ! [D_190] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_190) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(D_190,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',D_190,u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_190)
      | ~ r2_hidden('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_190,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_247])).

tff(c_254,plain,(
    ! [D_197] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',D_197) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(D_197,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',D_197,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_197)
      | ~ r2_hidden('#skF_1'(D_197,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(D_197,'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_250])).

tff(c_258,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_173,c_254])).

tff(c_261,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_28,c_26,c_258])).

tff(c_262,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_174,c_261])).

tff(c_263,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_266,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_266])).

tff(c_272,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_194,plain,(
    ! [C_182,D_181,E_185,A_183,B_184] :
      ( m1_subset_1('#skF_1'(D_181,C_182,A_183,B_184,E_185),A_183)
      | k2_partfun1(A_183,B_184,C_182,D_181) = E_185
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(D_181,B_184)))
      | ~ v1_funct_2(E_185,D_181,B_184)
      | ~ v1_funct_1(E_185)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(A_183))
      | v1_xboole_0(D_181)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(C_182,A_183,B_184)
      | ~ v1_funct_1(C_182)
      | v1_xboole_0(B_184)
      | v1_xboole_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_196,plain,(
    ! [C_182,A_183] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_182,A_183,u1_struct_0('#skF_2'),'#skF_6'),A_183)
      | k2_partfun1(A_183,u1_struct_0('#skF_2'),C_182,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_183))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_182,A_183,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_182)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_201,plain,(
    ! [C_182,A_183] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_182,A_183,u1_struct_0('#skF_2'),'#skF_6'),A_183)
      | k2_partfun1(A_183,u1_struct_0('#skF_2'),C_182,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_183))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_182,A_183,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_182)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_196])).

tff(c_202,plain,(
    ! [C_182,A_183] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),C_182,A_183,u1_struct_0('#skF_2'),'#skF_6'),A_183)
      | k2_partfun1(A_183,u1_struct_0('#skF_2'),C_182,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_183))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_182,A_183,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_182)
      | v1_xboole_0(A_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_174,c_201])).

tff(c_271,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3'))
    | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_273,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),'#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_281,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_202,c_273])).

tff(c_284,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_272,c_281])).

tff(c_285,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_284])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_96,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k2_partfun1(u1_struct_0(A_162),u1_struct_0(B_163),C_164,u1_struct_0(D_165)) = k2_tmap_1(A_162,B_163,C_164,D_165)
      | ~ m1_pre_topc(D_165,A_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(B_163))))
      | ~ v1_funct_2(C_164,u1_struct_0(A_162),u1_struct_0(B_163))
      | ~ v1_funct_1(C_164)
      | ~ l1_pre_topc(B_163)
      | ~ v2_pre_topc(B_163)
      | v2_struct_0(B_163)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_100,plain,(
    ! [D_165] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_165)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_165)
      | ~ m1_pre_topc(D_165,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_107,plain,(
    ! [D_165] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_165)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_165)
      | ~ m1_pre_topc(D_165,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_50,c_48,c_36,c_34,c_100])).

tff(c_108,plain,(
    ! [D_165] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_165)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_165)
      | ~ m1_pre_topc(D_165,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_107])).

tff(c_289,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6'
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_108])).

tff(c_296,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_289])).

tff(c_22,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_300,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_22])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_300])).

tff(c_304,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_314,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6'
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_108])).

tff(c_321,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_314])).

tff(c_325,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_22])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.98  
% 3.85/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.98  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.98  
% 3.85/1.98  %Foreground sorts:
% 3.85/1.98  
% 3.85/1.98  
% 3.85/1.98  %Background operators:
% 3.85/1.98  
% 3.85/1.98  
% 3.85/1.98  %Foreground operators:
% 3.85/1.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.98  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.98  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.98  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.98  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.98  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.85/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.85/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.98  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.98  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.85/1.98  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.85/1.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.98  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.85/1.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.98  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.85/1.98  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.85/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.98  
% 3.85/2.02  tff(f_175, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 3.85/2.02  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.85/2.02  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.85/2.02  tff(f_77, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, D, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((![F]: (m1_subset_1(F, A) => (r2_hidden(F, D) => (k3_funct_2(A, B, C, F) = k1_funct_1(E, F))))) => (k2_partfun1(A, B, C, D) = E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 3.85/2.02  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.85/2.02  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.85/2.02  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.85/2.02  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.85/2.02  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_28, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_72, plain, (![A_155, B_156, D_157]: (r2_funct_2(A_155, B_156, D_157, D_157) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(D_157, A_155, B_156) | ~v1_funct_1(D_157))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/2.02  tff(c_74, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_72])).
% 3.85/2.02  tff(c_79, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_74])).
% 3.85/2.02  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_12, plain, (![A_67]: (l1_struct_0(A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.85/2.02  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_119, plain, (![D_167, A_169, C_168, E_171, B_170]: (r2_hidden('#skF_1'(D_167, C_168, A_169, B_170, E_171), D_167) | k2_partfun1(A_169, B_170, C_168, D_167)=E_171 | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(D_167, B_170))) | ~v1_funct_2(E_171, D_167, B_170) | ~v1_funct_1(E_171) | ~m1_subset_1(D_167, k1_zfmisc_1(A_169)) | v1_xboole_0(D_167) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~v1_funct_2(C_168, A_169, B_170) | ~v1_funct_1(C_168) | v1_xboole_0(B_170) | v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/2.02  tff(c_121, plain, (![C_168, A_169]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_4')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_4'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_169)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_169))), inference(resolution, [status(thm)], [c_26, c_119])).
% 3.85/2.02  tff(c_126, plain, (![C_168, A_169]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_4')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_169)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_121])).
% 3.85/2.02  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_126])).
% 3.85/2.02  tff(c_16, plain, (![A_71]: (~v1_xboole_0(u1_struct_0(A_71)) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.85/2.02  tff(c_133, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_130, c_16])).
% 3.85/2.02  tff(c_136, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_133])).
% 3.85/2.02  tff(c_139, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_136])).
% 3.85/2.02  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_139])).
% 3.85/2.02  tff(c_145, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_126])).
% 3.85/2.02  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_123, plain, (![C_168, A_169]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_3')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_3'))='#skF_5' | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(A_169)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_169))), inference(resolution, [status(thm)], [c_32, c_119])).
% 3.85/2.02  tff(c_129, plain, (![C_168, A_169]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_3')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_3'))='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(A_169)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_123])).
% 3.85/2.02  tff(c_175, plain, (![C_168, A_169]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_3')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_3'))='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(A_169)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(A_169))), inference(negUnitSimplification, [status(thm)], [c_145, c_129])).
% 3.85/2.02  tff(c_176, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_175])).
% 3.85/2.02  tff(c_179, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_176, c_16])).
% 3.85/2.02  tff(c_182, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_179])).
% 3.85/2.02  tff(c_185, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_182])).
% 3.85/2.02  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_185])).
% 3.85/2.02  tff(c_191, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_175])).
% 3.85/2.02  tff(c_20, plain, (![B_89, A_87]: (m1_subset_1(u1_struct_0(B_89), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_pre_topc(B_89, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.85/2.02  tff(c_55, plain, (![B_150, A_151]: (l1_pre_topc(B_150) | ~m1_pre_topc(B_150, A_151) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.85/2.02  tff(c_58, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_55])).
% 3.85/2.02  tff(c_61, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_58])).
% 3.85/2.02  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_144, plain, (![C_168, A_169]: (v1_xboole_0(u1_struct_0('#skF_4')) | r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_4')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_169)) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(A_169))), inference(splitRight, [status(thm)], [c_126])).
% 3.85/2.02  tff(c_146, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_144])).
% 3.85/2.02  tff(c_162, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_146, c_16])).
% 3.85/2.02  tff(c_165, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_162])).
% 3.85/2.02  tff(c_168, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_165])).
% 3.85/2.02  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_168])).
% 3.85/2.02  tff(c_174, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_144])).
% 3.85/2.02  tff(c_173, plain, (![C_168, A_169]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), C_168, A_169, u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_4')) | k2_partfun1(A_169, u1_struct_0('#skF_2'), C_168, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_169)) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_168, A_169, u1_struct_0('#skF_2')) | ~v1_funct_1(C_168) | v1_xboole_0(A_169))), inference(splitRight, [status(thm)], [c_144])).
% 3.85/2.02  tff(c_24, plain, (![F_147]: (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', F_147)=k1_funct_1('#skF_6', F_147) | ~r2_hidden(F_147, u1_struct_0('#skF_4')) | ~m1_subset_1(F_147, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_241, plain, (![A_192, E_194, D_190, C_191, B_193]: (k3_funct_2(A_192, B_193, C_191, '#skF_1'(D_190, C_191, A_192, B_193, E_194))!=k1_funct_1(E_194, '#skF_1'(D_190, C_191, A_192, B_193, E_194)) | k2_partfun1(A_192, B_193, C_191, D_190)=E_194 | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(D_190, B_193))) | ~v1_funct_2(E_194, D_190, B_193) | ~v1_funct_1(E_194) | ~m1_subset_1(D_190, k1_zfmisc_1(A_192)) | v1_xboole_0(D_190) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(C_191, A_192, B_193) | ~v1_funct_1(C_191) | v1_xboole_0(B_193) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/2.02  tff(c_244, plain, (![E_194, D_190]: (k1_funct_1(E_194, '#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194))!=k1_funct_1('#skF_6', '#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194)) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_190)=E_194 | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(D_190, u1_struct_0('#skF_2')))) | ~v1_funct_2(E_194, D_190, u1_struct_0('#skF_2')) | ~v1_funct_1(E_194) | ~m1_subset_1(D_190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_190) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194), u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_241])).
% 3.85/2.02  tff(c_246, plain, (![E_194, D_190]: (k1_funct_1(E_194, '#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194))!=k1_funct_1('#skF_6', '#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194)) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_190)=E_194 | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(D_190, u1_struct_0('#skF_2')))) | ~v1_funct_2(E_194, D_190, u1_struct_0('#skF_2')) | ~v1_funct_1(E_194) | ~m1_subset_1(D_190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_190) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194), u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_244])).
% 3.85/2.02  tff(c_247, plain, (![E_194, D_190]: (k1_funct_1(E_194, '#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194))!=k1_funct_1('#skF_6', '#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194)) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_190)=E_194 | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(D_190, u1_struct_0('#skF_2')))) | ~v1_funct_2(E_194, D_190, u1_struct_0('#skF_2')) | ~v1_funct_1(E_194) | ~m1_subset_1(D_190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_190) | ~r2_hidden('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), E_194), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_191, c_145, c_246])).
% 3.85/2.02  tff(c_250, plain, (![D_190]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_190)='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(D_190, u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', D_190, u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_190) | ~r2_hidden('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_190, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3')))), inference(reflexivity, [status(thm), theory('equality')], [c_247])).
% 3.85/2.02  tff(c_254, plain, (![D_197]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', D_197)='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(D_197, u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', D_197, u1_struct_0('#skF_2')) | ~m1_subset_1(D_197, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_197) | ~r2_hidden('#skF_1'(D_197, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(D_197, '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_250])).
% 3.85/2.02  tff(c_258, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_173, c_254])).
% 3.85/2.02  tff(c_261, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_28, c_26, c_258])).
% 3.85/2.02  tff(c_262, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_191, c_174, c_261])).
% 3.85/2.02  tff(c_263, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_262])).
% 3.85/2.02  tff(c_266, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_263])).
% 3.85/2.02  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_266])).
% 3.85/2.02  tff(c_272, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_262])).
% 3.85/2.02  tff(c_194, plain, (![C_182, D_181, E_185, A_183, B_184]: (m1_subset_1('#skF_1'(D_181, C_182, A_183, B_184, E_185), A_183) | k2_partfun1(A_183, B_184, C_182, D_181)=E_185 | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(D_181, B_184))) | ~v1_funct_2(E_185, D_181, B_184) | ~v1_funct_1(E_185) | ~m1_subset_1(D_181, k1_zfmisc_1(A_183)) | v1_xboole_0(D_181) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(C_182, A_183, B_184) | ~v1_funct_1(C_182) | v1_xboole_0(B_184) | v1_xboole_0(A_183))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/2.02  tff(c_196, plain, (![C_182, A_183]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_182, A_183, u1_struct_0('#skF_2'), '#skF_6'), A_183) | k2_partfun1(A_183, u1_struct_0('#skF_2'), C_182, u1_struct_0('#skF_4'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_183)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_182, A_183, u1_struct_0('#skF_2')) | ~v1_funct_1(C_182) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_183))), inference(resolution, [status(thm)], [c_26, c_194])).
% 3.85/2.02  tff(c_201, plain, (![C_182, A_183]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_182, A_183, u1_struct_0('#skF_2'), '#skF_6'), A_183) | k2_partfun1(A_183, u1_struct_0('#skF_2'), C_182, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_183)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_182, A_183, u1_struct_0('#skF_2')) | ~v1_funct_1(C_182) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_196])).
% 3.85/2.02  tff(c_202, plain, (![C_182, A_183]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), C_182, A_183, u1_struct_0('#skF_2'), '#skF_6'), A_183) | k2_partfun1(A_183, u1_struct_0('#skF_2'), C_182, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_183)) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_182, A_183, u1_struct_0('#skF_2')) | ~v1_funct_1(C_182) | v1_xboole_0(A_183))), inference(negUnitSimplification, [status(thm)], [c_145, c_174, c_201])).
% 3.85/2.02  tff(c_271, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6'), inference(splitRight, [status(thm)], [c_262])).
% 3.85/2.02  tff(c_273, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), '#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_271])).
% 3.85/2.02  tff(c_281, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_202, c_273])).
% 3.85/2.02  tff(c_284, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_272, c_281])).
% 3.85/2.02  tff(c_285, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_191, c_284])).
% 3.85/2.02  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_96, plain, (![A_162, B_163, C_164, D_165]: (k2_partfun1(u1_struct_0(A_162), u1_struct_0(B_163), C_164, u1_struct_0(D_165))=k2_tmap_1(A_162, B_163, C_164, D_165) | ~m1_pre_topc(D_165, A_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162), u1_struct_0(B_163)))) | ~v1_funct_2(C_164, u1_struct_0(A_162), u1_struct_0(B_163)) | ~v1_funct_1(C_164) | ~l1_pre_topc(B_163) | ~v2_pre_topc(B_163) | v2_struct_0(B_163) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.85/2.02  tff(c_100, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_165))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_165) | ~m1_pre_topc(D_165, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_96])).
% 3.85/2.02  tff(c_107, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_165))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_165) | ~m1_pre_topc(D_165, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_50, c_48, c_36, c_34, c_100])).
% 3.85/2.02  tff(c_108, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_165))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_165) | ~m1_pre_topc(D_165, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_107])).
% 3.85/2.02  tff(c_289, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')='#skF_6' | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_285, c_108])).
% 3.85/2.02  tff(c_296, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_289])).
% 3.85/2.02  tff(c_22, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.85/2.02  tff(c_300, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_22])).
% 3.85/2.02  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_300])).
% 3.85/2.02  tff(c_304, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))='#skF_6'), inference(splitRight, [status(thm)], [c_271])).
% 3.85/2.02  tff(c_314, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')='#skF_6' | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_304, c_108])).
% 3.85/2.02  tff(c_321, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_314])).
% 3.85/2.02  tff(c_325, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_22])).
% 3.85/2.02  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_325])).
% 3.85/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/2.02  
% 3.85/2.02  Inference rules
% 3.85/2.02  ----------------------
% 3.85/2.02  #Ref     : 1
% 3.85/2.02  #Sup     : 45
% 3.85/2.02  #Fact    : 0
% 3.85/2.02  #Define  : 0
% 3.85/2.02  #Split   : 6
% 3.85/2.02  #Chain   : 0
% 3.85/2.02  #Close   : 0
% 3.85/2.02  
% 3.85/2.02  Ordering : KBO
% 3.85/2.02  
% 3.85/2.02  Simplification rules
% 3.85/2.02  ----------------------
% 3.85/2.02  #Subsume      : 0
% 3.85/2.02  #Demod        : 60
% 3.85/2.02  #Tautology    : 12
% 3.85/2.02  #SimpNegUnit  : 13
% 3.85/2.02  #BackRed      : 2
% 3.85/2.02  
% 3.85/2.02  #Partial instantiations: 0
% 3.85/2.02  #Strategies tried      : 1
% 3.85/2.02  
% 3.85/2.02  Timing (in seconds)
% 3.85/2.02  ----------------------
% 3.85/2.03  Preprocessing        : 0.53
% 4.10/2.03  Parsing              : 0.28
% 4.10/2.03  CNF conversion       : 0.06
% 4.10/2.03  Main loop            : 0.54
% 4.10/2.03  Inferencing          : 0.20
% 4.10/2.03  Reduction            : 0.16
% 4.10/2.03  Demodulation         : 0.11
% 4.10/2.03  BG Simplification    : 0.03
% 4.10/2.03  Subsumption          : 0.11
% 4.10/2.03  Abstraction          : 0.03
% 4.10/2.03  MUC search           : 0.00
% 4.10/2.03  Cooper               : 0.00
% 4.10/2.03  Total                : 1.16
% 4.10/2.03  Index Insertion      : 0.00
% 4.10/2.03  Index Deletion       : 0.00
% 4.10/2.03  Index Matching       : 0.00
% 4.10/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
